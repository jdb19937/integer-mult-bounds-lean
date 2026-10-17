module

public import IntegerMultBounds.MathlibTM2.Host.BinArithMul
import IntegerMultBounds.MathlibTM2.Host.Route

/-!
# Binary registers: restoring division and modular multiplication

`bdivmod a b q r bw rr t tx ty tz cy` divides `a` (width `La`, value `x`) by `b` (width `Lb`,
value `y > 0`): `q` gains `binSyms La (x / y)` and `r` gains `binSyms Lb (x % y)` on top; every
other register ends as it started.

Phases: `bw := b` with one high zero (width `W = Lb + 1`, `bcopy`, `bpad1`); `rr := W` zeros;
`a` moves reversed onto `t`, so its bits come most significant first; for each bit (`eachSym` of
`t` back onto `a`) the remainder shifts the bit in (`bshift`), a subtraction pass computes
`rr - bw` with the borrow in scan slot `cy` (`zipPass` of `subF`), and the difference replaces
`rr` exactly when there is no borrow, the quotient bit (no borrow) being pushed onto `q`
(`divIter_exec`, `12 W + 18` steps). After step `j` the remainder is `(x / 2 ^ (La - j)) % y`
and `q` holds the `j` bits of `(x / 2 ^ (La - j)) / y` (`div_step`). Finally `r` gains `rr`
without its top bit (`bmoveLow`) and `bw` is cleared.

`bdivmod_exec`: at most `La (12 Lb + 35) + 20 Lb + 36` steps.

`bmodmul a b m c p qq s rr t tx ty tz cy` computes `p := a * b` (`bmul`), divides `p` by `m`
(width `Lm`, value `M > 0`) into the quotient `qq` and the output `c`, and clears `qq` and `p`:
`c` gains `binSyms Lm ((x * y) % M)` on top (`bmodmul_exec`), in at most
`La (12 N + 20) + N (12 Lm + 35) + 20 N + 20 Lm + 64` steps for `N = La + Lb`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node


variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- Push the bit `b` onto register `q`. -/
def pushBit (q : Fin T) (b : Bool) : Act T Q A U := .push (.rt q) (fun _ => bitSymbol b) .done

lemma pushBit_run (q : Fin T) (b : Bool) (v : HS T Q A U) (S : Stacks T A) :
    (pushBit q b).run (mk v S) =
      mk v { S with R := Function.update S.R q (bitSymbol b :: S.R q) } := by
  simp only [pushBit, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk]

/-- One step of restoring division, with a dividend bit in `sym`: shift the bit into the
remainder `rr`, subtract the divisor `bw` with the borrow in slot `cy`, keep the difference when
there is no borrow, and push the quotient bit onto `q`. -/
def divIter (rr bw q tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (bshift rr tx (fun v => v.sym.getD blank))
    (.seq (zipPass rr bw tx ty tz cy subF false)
      (.seq (moveR ty bw id)
        (.cond (fun v => symBit (v.scan cy))
          (.seq (moveR tx rr id) (.seq (bclear tz) (.act (pushBit q false))))
          (.seq (moveR tz rr id) (.seq (bclear tx) (.act (pushBit q true)))))))

/-- `divIter` in width `W`, with remainder `ρ`, divisor `y` and the bit `bit` in `sym`, where
`u = 2 ρ + bit < 2 ^ W`: `rr := u - y` if `y ≤ u`, else `u`; `q` gains the bit `y ≤ u`; exactly
`12 W + 18` steps. -/
theorem divIter_exec {rr bw q tx ty tz cy : Fin T} (hreg : [rr, bw, q, tx, ty, tz].Nodup)
    (hcr : cy ≠ rr) (hcb : cy ≠ bw) {W ρ y : ℕ} (bit : Bool) (hu : 2 * ρ + bit.toNat < 2 ^ W)
    (hy : y < 2 ^ W) (v : HS T Q A U) (S : Stacks T A) (hsym : v.sym = some (bitSymbol bit))
    (hr : S.R rr = binSyms W ρ) (hb : S.R bw = binSyms W y) (htx : S.R tx = [])
    (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (divIter rr bw q tx ty tz cy) (mk v S) (12 * W + 18)
        (mk v' { S with
          R := Function.update (Function.update S.R rr
              (binSyms W (if y ≤ 2 * ρ + bit.toNat then 2 * ρ + bit.toNat - y
                else 2 * ρ + bit.toNat)))
            q (bitSymbol (decide (y ≤ 2 * ρ + bit.toNat)) :: S.R q) }) := by
  have hreg' := hreg
  regs_ne hreg'
  set u := 2 * ρ + bit.toNat with hu_def
  -- shift the bit in
  obtain ⟨v₁, hu₁, he₁⟩ := bshift_exec body ‹rr ≠ tx› (fun v => v.sym.getD blank) v S htx
  rw [hsym, Option.getD_some, hr, binSyms_shift, ← hu_def] at he₁
  set R₁ := Function.update S.R rr (binSyms W u) with hR₁
  -- subtract
  obtain ⟨v₂, hu₂, hc₂, -, he₂⟩ := zipPass_exec body (x := rr) (y := bw) (tx := tx) (ty := ty)
    (tz := tz) (by regs_nodup) hcr hcb subF false (L := W) (a := u) (b := y) v₁
    { S with R := R₁ } (by simp [hR₁]) (by simp [Function.update_of_ne, *, Ne.symm])
  rw [zipFin_subF_binBits W u y hu hy] at hc₂
  rw [zipOut_subF_binBits W u y hy] at he₂
  set R₂ := zipRegs R₁ rr bw tx ty tz (binBits W u) (binBits W y) (binBits W (u + 2 ^ W - y))
    with hR₂
  -- restore the divisor
  obtain ⟨v₃, hu₃, hsc₃, he₃⟩ := moveR_exec_scan body ty bw (Ne.symm ‹bw ≠ ty›) id v₂
    { S with R := R₂ }
  set R₃ := movedR R₂ ty bw id (R₂ ty) with hR₃
  have hc₃ : symBit ((mk v₃ { S with R := R₃ } : Store _ _).var.scan cy) = decide (u < y) := by
    simp [hsc₃, hc₂]
  have h2tx : R₂ tx = (binSyms W u).reverse := by
    rw [hR₂, zipRegs, hR₁, Function.update_of_ne ‹tx ≠ tz›, Function.update_of_ne ‹tx ≠ ty›,
      Function.update_self, Function.update_of_ne ‹rr ≠ tx›.symm, htx, List.append_nil, binSyms_eq]
  have h2tz : R₂ tz = (binSyms W (u + 2 ^ W - y)).reverse := by
    rw [hR₂, zipRegs, hR₁, Function.update_self, Function.update_of_ne ‹rr ≠ tz›.symm, htz,
      List.append_nil, binSyms_eq]
  have h3tx : R₃ tx = (binSyms W u).reverse := by
    rw [hR₃, movedR, Function.update_of_ne ‹bw ≠ tx›.symm, Function.update_of_ne ‹tx ≠ ty›, h2tx]
  have h3tz : R₃ tz = (binSyms W (u + 2 ^ W - y)).reverse := by
    rw [hR₃, movedR, Function.update_of_ne ‹bw ≠ tz›.symm, Function.update_of_ne ‹ty ≠ tz›.symm,
      h2tz]
  have h2ty : (R₂ ty).length = W := by
    simp [zipRegs, Function.update_of_ne, *, Ne.symm]
  have h3 : ∀ k, k ≠ rr → k ≠ tx → k ≠ tz → R₃ k = S.R k := by
    intro k h1 h2 h3
    simp only [hR₃, hR₂, hR₁, zipRegs, movedR, Function.update_apply]
    split_ifs <;> simp_all [binSyms_eq]
  have h3rr : R₃ rr = [] := by
    simp only [hR₃, hR₂, hR₁, zipRegs, movedR, Function.update_apply]
    split_ifs <;> simp_all
  by_cases hlt : u < y
  · -- borrow: keep the shifted remainder, quotient bit `0`
    obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body tx rr (Ne.symm ‹rr ≠ tx›) id v₃ { S with R := R₃ }
    set R₄ := movedR R₃ tx rr id (R₃ tx) with hR₄
    obtain ⟨v₅, hu₅, -, he₅⟩ := bclear_exec body tz v₄ { S with R := R₄ }
    have he₆ := Exec.act (body := body) (pushBit q false)
      (mk v₅ { S with R := Function.update R₄ tz [] })
    rw [pushBit_run] at he₆
    have hcond := Exec.cond_true (body := body) (f := fun v => symBit (v.scan cy)) (q := .seq (moveR tz rr id)
      (.seq (bclear tx) (.act (pushBit q true)))) (by rw [hc₃]; simpa using hlt)
      (Exec.seq he₄ (Exec.seq he₅ he₆))
    refine ⟨v₅, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂
      (Exec.seq he₃ hcond))) ?_ ?_⟩
    · have h4tz : R₄ tz = (binSyms W (u + 2 ^ W - y)).reverse := by
        rw [hR₄, movedR, Function.update_of_ne ‹rr ≠ tz›.symm, Function.update_of_ne ‹tx ≠ tz›.symm,
          h3tz]
      dsimp only
      rw [h2ty, h3tx, h4tz]
      simp only [length_binSyms, List.length_reverse]
      omega
    · have hle : ¬ y ≤ u := by omega
      have h4rr : R₄ rr = binSyms W u := by
        rw [hR₄, movedR, Function.update_self, h3tx, h3rr, List.map_id, List.reverse_reverse,
          List.append_nil]
      have h4 : ∀ k, k ≠ rr → k ≠ tx → k ≠ tz → R₄ k = S.R k := by
        intro k h1 h2 h3'
        rw [hR₄, movedR, Function.update_of_ne h1, Function.update_of_ne h2, h3 k h1 h2 h3']
      have h4tx : R₄ tx = [] := by
        rw [hR₄, movedR, Function.update_of_ne ‹rr ≠ tx›.symm, Function.update_self]
      congr 2
      simp only [hle, ↓reduceIte, decide_false]
      funext k
      by_cases hkq : k = q
      · subst hkq
        rw [Function.update_self, Function.update_self, Function.update_of_ne ‹k ≠ tz›,
          h4 k ‹rr ≠ k›.symm ‹k ≠ tx› ‹k ≠ tz›]
      rw [Function.update_of_ne hkq, Function.update_of_ne hkq]
      by_cases hkz : k = tz
      · subst hkz; rw [Function.update_self, Function.update_of_ne ‹rr ≠ k›.symm, htz]
      rw [Function.update_of_ne hkz]
      by_cases hkr : k = rr
      · subst hkr; rw [Function.update_self, h4rr]
      rw [Function.update_of_ne hkr]
      by_cases hkx : k = tx
      · subst hkx; rw [h4tx, htx]
      exact h4 k hkr hkx hkz
  · -- no borrow: the difference replaces the remainder, quotient bit `1`
    obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body tz rr (Ne.symm ‹rr ≠ tz›) id v₃ { S with R := R₃ }
    set R₄ := movedR R₃ tz rr id (R₃ tz) with hR₄
    obtain ⟨v₅, hu₅, -, he₅⟩ := bclear_exec body tx v₄ { S with R := R₄ }
    have he₆ := Exec.act (body := body) (pushBit q true)
      (mk v₅ { S with R := Function.update R₄ tx [] })
    rw [pushBit_run] at he₆
    have hcond := Exec.cond_false (body := body) (f := fun v => symBit (v.scan cy)) (p := .seq (moveR tx rr id)
      (.seq (bclear tz) (.act (pushBit q false)))) (by rw [hc₃]; simpa using hlt)
      (Exec.seq he₄ (Exec.seq he₅ he₆))
    refine ⟨v₅, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂
      (Exec.seq he₃ hcond))) ?_ ?_⟩
    · have h4tx : R₄ tx = (binSyms W u).reverse := by
        rw [hR₄, movedR, Function.update_of_ne ‹rr ≠ tx›.symm, Function.update_of_ne ‹tx ≠ tz›,
          h3tx]
      dsimp only
      rw [h2ty, h3tz, h4tx]
      simp only [length_binSyms, List.length_reverse]
      omega
    · have hle : y ≤ u := by omega
      have hmod : (binSyms W (u + 2 ^ W - y) : List (Fin (A + 4))) = binSyms W (u - y) := by
        rw [← binSyms_mod, show u + 2 ^ W - y = u - y + 2 ^ W by omega, Nat.add_mod_right,
          binSyms_mod]
      have h4rr : R₄ rr = binSyms W (u - y) := by
        rw [hR₄, movedR, Function.update_self, h3tz, h3rr, List.map_id, List.reverse_reverse,
          List.append_nil, hmod]
      have h4 : ∀ k, k ≠ rr → k ≠ tx → k ≠ tz → R₄ k = S.R k := by
        intro k h1 h2 h3'
        rw [hR₄, movedR, Function.update_of_ne h1, Function.update_of_ne h3', h3 k h1 h2 h3']
      have h4tz : R₄ tz = [] := by
        rw [hR₄, movedR, Function.update_of_ne ‹rr ≠ tz›.symm, Function.update_self]
      congr 2
      simp only [hle, ↓reduceIte, decide_true]
      funext k
      by_cases hkq : k = q
      · subst hkq
        rw [Function.update_self, Function.update_self, Function.update_of_ne ‹k ≠ tx›,
          h4 k ‹rr ≠ k›.symm ‹k ≠ tx› ‹k ≠ tz›]
      rw [Function.update_of_ne hkq, Function.update_of_ne hkq]
      by_cases hkx : k = tx
      · subst hkx; rw [Function.update_self, Function.update_of_ne ‹rr ≠ k›.symm, htx]
      rw [Function.update_of_ne hkx]
      by_cases hkr : k = rr
      · subst hkr; rw [Function.update_self, h4rr]
      rw [Function.update_of_ne hkr]
      by_cases hkz : k = tz
      · subst hkz; rw [h4tz, htz]
      exact h4 k hkr hkx hkz

/-- A quotient bit below a binary value: `binSyms (j + 1) (2 m + b) = b :: binSyms j m`. -/
lemma binSyms_two_mul_add (j m : ℕ) (b : Bool) :
    (binSyms (j + 1) (2 * m + b.toNat) : List (Fin (A + 4))) = bitSymbol b :: binSyms j m := by
  rw [binSyms_succ]
  congr 2
  · cases b <;> simp [Nat.testBit_zero]
  · cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Restoring division of `a` by `b` (`b > 0`): `q` gains the quotient and `r` the remainder. -/
def bdivmod (a b q r bw rr t tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (bcopy b bw tx ty)
    (.seq (bpad1 bw tx)
      (.seq (bzero bw rr tx)
        (.seq (moveR a t id)
          (.seq (eachSym t a (divIter rr bw q tx ty tz cy))
            (.seq (bmoveLow rr tx r) (bclear bw))))))

/-- `bdivmod`: `a` holding `binSyms La x` and `b` holding `binSyms Lb y` with `0 < y`
(`x < 2 ^ La`, `y < 2 ^ Lb`); `q` gains `binSyms La (x / y)` and `r` gains `binSyms Lb (x % y)`
on top, every other register ends as it started, in at most `La (12 Lb + 35) + 20 Lb + 36`
steps. Scan slot `cy` (outside `rr`, `bw`) carries the borrows; the scan slots `rr`, `bw` are
scratch. -/
theorem bdivmod_exec {a b q r bw rr t tx ty tz cy : Fin T}
    (hreg : [a, b, q, r, bw, rr, t, tx, ty, tz].Nodup) (hcr : cy ≠ rr) (hcb : cy ≠ bw)
    {La Lb x y : ℕ} (hx : x < 2 ^ La) (hy : y < 2 ^ Lb) (hy0 : 0 < y) (v : HS T Q A U)
    (S : Stacks T A) (ha : S.R a = binSyms La x) (hb : S.R b = binSyms Lb y) (hbw : S.R bw = [])
    (hrr : S.R rr = []) (ht : S.R t = []) (htx : S.R tx = []) (hty : S.R ty = [])
    (htz : S.R tz = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ La * (12 * Lb + 35) + 20 * Lb + 36 ∧
      Exec body (bdivmod a b q r bw rr t tx ty tz cy) (mk v S) m
        (mk v' { S with
          R := Function.update (Function.update S.R q (binSyms La (x / y) ++ S.R q)) r
            (binSyms Lb (x % y) ++ S.R r) }) := by
  have hreg' := hreg
  regs_ne hreg'
  set W := Lb + 1 with hW
  -- `bw := b` with one high zero
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body (a := b) (c := bw) (t₁ := tx) (t₂ := ty)
    (by regs_nodup) v S htx hty
  rw [hb, hbw, List.append_nil, length_binSyms] at he₁
  set R₁ := Function.update S.R bw (binSyms Lb y) with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := bpad1_exec body (a := bw) (t := tx) ‹bw ≠ tx› hy v₁ { S with R := R₁ }
    (by simp [hR₁]) (by simp [hR₁, Function.update_of_ne ‹bw ≠ tx›.symm, htx])
  set R₂ := Function.update R₁ bw (binSyms W y) with hR₂
  -- `rr := W` zeros
  obtain ⟨v₃, hu₃, he₃⟩ := bzero_exec body (wR := bw) (c := rr) (t := tx) (by regs_nodup) v₂
    { S with R := R₂ } (by simp [hR₂, hR₁, Function.update_of_ne ‹bw ≠ tx›.symm, htx])
  have h2rr : R₂ rr = [] := by
    simp [hR₂, hR₁, Function.update_of_ne ‹bw ≠ rr›.symm, hrr]
  dsimp only at he₃
  rw [h2rr, List.append_nil, show R₂ bw = binSyms W y by simp [hR₂], length_binSyms] at he₃
  set R₃ := Function.update R₂ rr (binSyms W 0) with hR₃
  -- the dividend, most significant bit on top
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body a t ‹a ≠ t› id v₃ { S with R := R₃ }
  have h3a : R₃ a = binSyms La x := by
    simp [hR₃, hR₂, hR₁, Function.update_of_ne ‹a ≠ rr›, Function.update_of_ne ‹a ≠ bw›, ha]
  have h3t : R₃ t = [] := by
    simp [hR₃, hR₂, hR₁, Function.update_of_ne ‹rr ≠ t›.symm, Function.update_of_ne ‹bw ≠ t›.symm, ht]
  dsimp only at he₄
  rw [h3a, length_binSyms] at he₄
  set R₄ := movedR R₃ a t id (binSyms La x) with hR₄
  have h4t : R₄ t = (binSyms La x).reverse := by simp [hR₄, movedR, h3t]
  have h4a : R₄ a = [] := by simp [hR₄, movedR, Function.update_of_ne ‹a ≠ t›]
  have h4 : ∀ k, k ≠ a → k ≠ t → k ≠ rr → k ≠ bw → R₄ k = S.R k := by
    intro k h1 h2 h3 h4
    simp only [hR₄, hR₃, hR₂, hR₁, movedR, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4]
  have h4rr : R₄ rr = binSyms W 0 := by
    simp [hR₄, hR₃, movedR, Function.update_of_ne ‹a ≠ rr›.symm, Function.update_of_ne ‹rr ≠ t›]
  have h4bw : R₄ bw = binSyms W y := by
    simp [hR₄, hR₃, hR₂, movedR, Function.update_of_ne ‹a ≠ bw›.symm,
      Function.update_of_ne ‹bw ≠ t›, Function.update_of_ne ‹bw ≠ rr›]
  -- the division loop
  let hi : ℕ → ℕ := fun j => x / 2 ^ (La - j)
  let Ψ : ℕ → Regs T A := fun j =>
    Function.update (Function.update R₄ rr (binSyms W (hi j % y))) q
      (binSyms j (hi j / y) ++ S.R q)
  have hp : SymSpec body (divIter rr bw q tx ty tz cy) t a (R₄ t) Ψ (12 * W + 18) := by
    intro j hj w S' hsym hS'
    rw [h4t, List.length_reverse, length_binSyms] at hj
    have hbit : (R₄ t)[j] = bitSymbol (x.testBit (La - 1 - j)) := by
      simp only [h4t, getElem_reverse_binSyms]
    have hhi : hi (j + 1) = 2 * hi j + (x.testBit (La - 1 - j)).toNat := by
      simp only [hi]
      rw [show La - (j + 1) = La - 1 - j by omega, div_two_pow_eq x (La - 1 - j),
        show La - 1 - j + 1 = La - j by omega]
    have hρ : hi j % y < y := Nat.mod_lt _ hy0
    have hpow : 2 ^ W = 2 * 2 ^ Lb := by rw [hW, pow_succ]; ring
    have hbitle := Bool.toNat_le (x.testBit (La - 1 - j))
    have hSq : S'.R q = Ψ j q := hS' q ‹q ≠ t› ‹a ≠ q›.symm
    obtain ⟨w', hw', he⟩ := divIter_exec body (rr := rr) (bw := bw) (q := q) (tx := tx) (ty := ty)
      (tz := tz) (by regs_nodup) hcr hcb (W := W) (ρ := hi j % y) (y := y)
      (x.testBit (La - 1 - j)) (by omega) (by omega) w S' (by rw [hsym, hbit])
      (by rw [hS' rr ‹rr ≠ t› ‹a ≠ rr›.symm]; simp [Ψ, Function.update_of_ne ‹q ≠ rr›.symm])
      (by rw [hS' bw ‹bw ≠ t› ‹a ≠ bw›.symm]
          simp [Ψ, Function.update_of_ne ‹q ≠ bw›.symm, Function.update_of_ne ‹bw ≠ rr›, h4bw])
      (by rw [hS' tx ‹t ≠ tx›.symm ‹a ≠ tx›.symm]
          simp [Ψ, Function.update_of_ne ‹q ≠ tx›.symm, Function.update_of_ne ‹rr ≠ tx›.symm,
            h4 tx ‹a ≠ tx›.symm ‹t ≠ tx›.symm ‹rr ≠ tx›.symm ‹bw ≠ tx›.symm, htx])
      (by rw [hS' ty ‹t ≠ ty›.symm ‹a ≠ ty›.symm]
          simp [Ψ, Function.update_of_ne ‹q ≠ ty›.symm, Function.update_of_ne ‹rr ≠ ty›.symm,
            h4 ty ‹a ≠ ty›.symm ‹t ≠ ty›.symm ‹rr ≠ ty›.symm ‹bw ≠ ty›.symm, hty])
      (by rw [hS' tz ‹t ≠ tz›.symm ‹a ≠ tz›.symm]
          simp [Ψ, Function.update_of_ne ‹q ≠ tz›.symm, Function.update_of_ne ‹rr ≠ tz›.symm,
            h4 tz ‹a ≠ tz›.symm ‹t ≠ tz›.symm ‹rr ≠ tz›.symm ‹bw ≠ tz›.symm, htz])
    obtain ⟨hdiv, hmod⟩ := div_step y (hi j) (x.testBit (La - 1 - j)) hy0
    refine ⟨w', _, _, hw', le_refl _, he, ?_, ?_, fun k hkt hka => ?_⟩
    · simp [Function.update_of_ne ‹q ≠ t›.symm, Function.update_of_ne ‹rr ≠ t›.symm]
    · simp [Function.update_of_ne ‹a ≠ q›, Function.update_of_ne ‹a ≠ rr›]
    · by_cases hkq : k = q
      · subst hkq
        rw [Function.update_self, hSq]
        simp only [Ψ, Function.update_self, hhi, hdiv]
        rw [← List.cons_append, ← binSyms_two_mul_add]
      rw [Function.update_of_ne hkq]
      by_cases hkr : k = rr
      · subst hkr
        rw [Function.update_self]
        simp only [Ψ, Function.update_of_ne hkq, Function.update_self, hhi, hmod]
      rw [Function.update_of_ne hkr, hS' k hkt hka]
      simp only [Ψ, Function.update_of_ne hkq, Function.update_of_ne hkr]
  obtain ⟨v₅, R₅, m₅, hu₅, hm₅, he₅, ht₅, ha₅, hΨ₅⟩ := eachSym_exec body ‹a ≠ t›.symm v₄
    { S with R := R₄ } hp (fun k hkt hka => by
      dsimp only
      by_cases hkq : k = q
      · subst hkq
        simp [Ψ, binSyms, h4 k ‹a ≠ k›.symm ‹k ≠ t› ‹k ≠ rr› ‹k ≠ bw›]
      by_cases hkr : k = rr
      · subst hkr
        simp only [Ψ, Function.update_of_ne hkq, Function.update_self, hi, Nat.sub_zero,
          Nat.div_eq_of_lt hx, Nat.zero_mod, h4rr]
      simp only [Ψ, Function.update_of_ne hkq, Function.update_of_ne hkr])
  dsimp only at hm₅ ht₅ ha₅ hΨ₅
  rw [h4t, List.length_reverse, length_binSyms] at hm₅ hΨ₅
  rw [h4t, h4a, List.reverse_reverse, List.append_nil] at ha₅
  have h5rr : R₅ rr = binSyms W (x % y) := by
    rw [hΨ₅ rr ‹rr ≠ t› ‹a ≠ rr›.symm]
    simp [Ψ, hi, Function.update_of_ne ‹q ≠ rr›.symm]
  have h5q : R₅ q = binSyms La (x / y) ++ S.R q := by
    rw [hΨ₅ q ‹q ≠ t› ‹a ≠ q›.symm]
    simp [Ψ, hi]
  -- the remainder without its top bit onto `r`, and clear `bw`
  obtain ⟨v₆, hu₆, he₆⟩ := bmoveLow_exec body (s := rr) (t := tx) (d := r) ‹rr ≠ tx› ‹r ≠ tx› v₅
    { S with R := R₅ } (by
      show R₅ tx = []
      rw [hΨ₅ tx ‹t ≠ tx›.symm ‹a ≠ tx›.symm]
      simp [Ψ, Function.update_of_ne ‹q ≠ tx›.symm, Function.update_of_ne ‹rr ≠ tx›.symm,
        h4 tx ‹a ≠ tx›.symm ‹t ≠ tx›.symm ‹rr ≠ tx›.symm ‹bw ≠ tx›.symm, htx])
  dsimp only at he₆
  rw [h5rr, hW, binSyms_dropLast, length_binSyms] at he₆
  obtain ⟨v₇, hu₇, -, he₇⟩ := bclear_exec body bw v₆
    { S with
      R := Function.update (Function.update R₅ rr []) r
        (binSyms Lb (x % y) ++ Function.update R₅ rr [] r) }
  have h6bw : (Function.update (Function.update R₅ rr []) r
      (binSyms Lb (x % y) ++ Function.update R₅ rr [] r)) bw = binSyms W y := by
    rw [Function.update_of_ne ‹r ≠ bw›.symm, Function.update_of_ne ‹bw ≠ rr›,
      hΨ₅ bw ‹bw ≠ t› ‹a ≠ bw›.symm]
    simp [Ψ, Function.update_of_ne ‹q ≠ bw›.symm, Function.update_of_ne ‹bw ≠ rr›, h4bw]
  refine ⟨v₇, _, by rw [hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁
    (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆ he₇)))))) rfl ?_⟩
  · dsimp only
    rw [h6bw, length_binSyms]
    simp only [hW, Nat.add_sub_cancel] at hm₅ ⊢
    nlinarith [hm₅]
  · congr 2
    funext k
    dsimp only
    by_cases hkbw : k = bw
    · subst hkbw
      rw [Function.update_self, Function.update_of_ne ‹r ≠ k›.symm,
        Function.update_of_ne ‹q ≠ k›.symm, hbw]
    rw [Function.update_of_ne hkbw]
    by_cases hkr : k = r
    · subst hkr
      rw [Function.update_self, Function.update_self, Function.update_of_ne ‹k ≠ rr›,
        hΨ₅ k ‹k ≠ t› ‹a ≠ k›.symm]
      simp [Ψ, Function.update_of_ne ‹q ≠ k›.symm, Function.update_of_ne ‹k ≠ rr›,
        h4 k ‹a ≠ k›.symm ‹k ≠ t› ‹k ≠ rr› ‹k ≠ bw›]
    rw [Function.update_of_ne hkr, Function.update_of_ne hkr]
    by_cases hkrr : k = rr
    · subst hkrr
      rw [Function.update_self, Function.update_of_ne ‹q ≠ k›.symm, hrr]
    rw [Function.update_of_ne hkrr]
    by_cases hkq : k = q
    · subst hkq; rw [Function.update_self, h5q]
    rw [Function.update_of_ne hkq]
    by_cases hka : k = a
    · subst hka; rw [ha₅, ha]
    by_cases hkt : k = t
    · subst hkt; rw [ht₅, ht]
    rw [hΨ₅ k hkt hka]
    simp only [Ψ, Function.update_of_ne hkq, Function.update_of_ne hkrr]
    exact h4 k hka hkt hkrr hkbw

/-- Modular multiplication: `p := a * b`, then `p` is divided by `m` with the remainder pushed
onto `c`; the quotient register `qq` and `p` are cleared. -/
def bmodmul (a b m c p qq s rr t tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (bmul a b p s t tx ty tz cy)
    (.seq (bdivmod p m qq c s rr t tx ty tz cy) (.seq (bclear qq) (bclear p)))

/-- `bmodmul`: `a`, `b`, `m` holding `binSyms La x`, `binSyms Lb y`, `binSyms Lm M` with
`0 < M`; `c` gains `binSyms Lm ((x * y) % M)` on top and every other register ends as it
started, in at most `La (12 N + 20) + N (12 Lm + 35) + 20 N + 20 Lm + 64` steps, `N = La + Lb`.
Scan slot `cy` lies outside `p`, `s`, `rr`. -/
theorem bmodmul_exec {a b m c p qq s rr t tx ty tz cy : Fin T}
    (hreg : [a, b, m, c, p, qq, s, rr, t, tx, ty, tz].Nodup) (hcp : cy ≠ p) (hcs : cy ≠ s)
    (hcr : cy ≠ rr) {La Lb Lm x y M : ℕ} (hx : x < 2 ^ La) (hy : y < 2 ^ Lb) (hM : M < 2 ^ Lm)
    (hM0 : 0 < M) (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms La x)
    (hb : S.R b = binSyms Lb y) (hm : S.R m = binSyms Lm M) (hp : S.R p = [])
    (hqq : S.R qq = []) (hs : S.R s = []) (hrr : S.R rr = []) (ht : S.R t = [])
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ (v' : HS T Q A U) (n : ℕ), v'.user = v.user ∧
      n ≤ La * (12 * (La + Lb) + 20) + (La + Lb) * (12 * Lm + 35) + 20 * (La + Lb) +
        20 * Lm + 64 ∧
      Exec body (bmodmul a b m c p qq s rr t tx ty tz cy) (mk v S) n
        (mk v' { S with R := Function.update S.R c (binSyms Lm ((x * y) % M) ++ S.R c) }) := by
  have hreg' := hreg
  regs_ne hreg'
  -- `p := a * b`
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := bmul_exec body (a := a) (b := b) (c := p) (s := s) (t := t)
    (tx := tx) (ty := ty) (tz := tz) (by regs_nodup) hcp hcs hx hy v S ha hb hp hs ht htx hty htz
  set R₁ := Function.update S.R p (binSyms (La + Lb) (x * y)) with hR₁
  have hxy : x * y < 2 ^ (La + Lb) := by
    rw [pow_add]; exact Nat.mul_lt_mul_of_lt_of_lt hx hy
  -- divide by `m`
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := bdivmod_exec body (a := p) (b := m) (q := qq) (r := c)
    (bw := s) (rr := rr) (t := t) (tx := tx) (ty := ty) (tz := tz) (by regs_nodup) hcr hcs hxy hM
    hM0 v₁ { S with R := R₁ } (by simp [hR₁])
    (by simp [hR₁, Function.update_of_ne ‹m ≠ p›, hm])
    (by simp [hR₁, Function.update_of_ne ‹p ≠ s›.symm, hs])
    (by simp [hR₁, Function.update_of_ne ‹p ≠ rr›.symm, hrr])
    (by simp [hR₁, Function.update_of_ne ‹p ≠ t›.symm, ht])
    (by simp [hR₁, Function.update_of_ne ‹p ≠ tx›.symm, htx])
    (by simp [hR₁, Function.update_of_ne ‹p ≠ ty›.symm, hty])
    (by simp [hR₁, Function.update_of_ne ‹p ≠ tz›.symm, htz])
  set R₂ := Function.update (Function.update R₁ qq (binSyms (La + Lb) (x * y / M) ++ R₁ qq)) c
    (binSyms Lm (x * y % M) ++ R₁ c) with hR₂
  -- clear the quotient and the product
  obtain ⟨v₃, hu₃, -, he₃⟩ := bclear_exec body qq v₂ { S with R := R₂ }
  obtain ⟨v₄, hu₄, -, he₄⟩ := bclear_exec body p v₃ { S with R := Function.update R₂ qq [] }
  have h2qq : R₂ qq = binSyms (La + Lb) (x * y / M) := by
    simp [hR₂, hR₁, Function.update_of_ne ‹c ≠ qq›.symm, Function.update_of_ne ‹p ≠ qq›.symm, hqq]
  have h2p : (Function.update R₂ qq []) p = binSyms (La + Lb) (x * y) := by
    simp [hR₂, hR₁, Function.update_of_ne ‹p ≠ qq›, Function.update_of_ne ‹c ≠ p›.symm]
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))) rfl ?_⟩
  · dsimp only
    rw [h2qq, h2p]
    simp only [length_binSyms]
    nlinarith [hn₁, hn₂]
  · congr 2
    funext k
    dsimp only
    by_cases hkp : k = p
    · subst hkp
      rw [Function.update_self, Function.update_of_ne ‹c ≠ k›.symm, hp]
    rw [Function.update_of_ne hkp]
    by_cases hkq : k = qq
    · subst hkq
      rw [Function.update_self, Function.update_of_ne ‹c ≠ k›.symm, hqq]
    rw [Function.update_of_ne hkq]
    by_cases hkc : k = c
    · subst hkc
      rw [hR₂, Function.update_self, Function.update_self, hR₁, Function.update_of_ne ‹k ≠ p›]
    rw [hR₂, Function.update_of_ne hkc, Function.update_of_ne hkc, Function.update_of_ne hkq, hR₁,
      Function.update_of_ne hkp]

end IntegerMultBounds.MathlibTM2.Host
