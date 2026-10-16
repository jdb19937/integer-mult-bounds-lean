module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-!
# Binary registers: schoolbook multiplication

`bmul a b c s t tx ty tz cy` multiplies `a` (width `La`, value `x`) by `b` (width `Lb`, value `y`)
into the empty register `c`, which ends holding `binSyms (La + Lb) (x * y)`; every other register
ends as it started.

Phases: `s := b` padded with `La` high zeros (width `W = Lb + La`, `bcopy`, `bpad`); `c := W`
zeros (`bzero`); then for each bit `x_j` of `a`, least significant first (`eachSym` through `t`),
`c := c + s` when `x_j` is set (`baddTo`, through `tx`, `ty`, `tz`, carry in scan slot `cy`) and
`s := 2 s` (`bshift`), both modulo `2 ^ W` (`mulIter_exec`); finally `a` is restored from `t` and
`s` cleared. After step `j`, `c` holds `y (x mod 2 ^ j)` and `s` holds `2 ^ j y`.

`bmul_exec`: at most `La (12 (La + Lb) + 20) + 16 (La + Lb) + 24` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node


variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- The low `j + 1` bits of `x`: the low `j` bits and bit `j`. -/
lemma mod_two_pow_succ_testBit (x j : ℕ) :
    x % 2 ^ (j + 1) = x % 2 ^ j + 2 ^ j * (x.testBit j).toNat := by
  rw [Nat.mod_pow_succ]
  congr 2
  have h : x.testBit j = (x / 2 ^ j).testBit 0 := by rw [Nat.testBit_div_two_pow, Nat.zero_add]
  rw [h]
  generalize x / 2 ^ j = n
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.testBit_zero, h]

/-- One step of the multiplication loop, with a bit in `sym`: if the bit is set, `c := c + s`;
then `s := 2 s`. -/
def mulIter (c s tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (.cond (fun v => symBit (v.sym.getD blank)) (baddTo c s tx ty tz cy) (.act .done))
    (bshift s tx (fun _ => bitSymbol false))

/-- `mulIter` in width `W` with the bit `bit` in `sym`: `c := u + bit · w` and `s := 2 w`
(modulo `2 ^ W`), in at most `12 W + 17` steps. -/
theorem mulIter_exec {c s tx ty tz cy : Fin T} (hreg : [c, s, tx, ty, tz].Nodup) (hcc : cy ≠ c)
    (hcs : cy ≠ s) {W u w : ℕ} (hu : u < 2 ^ W) (hw : w < 2 ^ W) (bit : Bool) (v : HS T Q A U)
    (S : Stacks T A) (hsym : v.sym = some (bitSymbol bit)) (hc : S.R c = binSyms W u)
    (hs : S.R s = binSyms W w) (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 12 * W + 17 ∧
      Exec body (mulIter c s tx ty tz cy) (mk v S) m
        (mk v' { S with
          R := Function.update (Function.update S.R c (binSyms W (u + bit.toNat * w))) s
            (binSyms W (2 * w)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hsym' : symBit ((mk v S).var.sym.getD blank) = bit := by simp [hsym]
  cases bit with
  | true =>
      obtain ⟨v₁, hu₁, -, -, he₁⟩ := baddTo_exec body hreg hcc hcs hu hw v S hc hs htx hty htz
      rw [binSyms_mod] at he₁
      obtain ⟨v₂, hu₂, he₂⟩ := bshift_exec body ‹s ≠ tx› (fun _ => bitSymbol false) v₁
        { S with R := Function.update S.R c (binSyms W (u + w)) }
        (by simp [Function.update_of_ne, *, Ne.symm])
      refine ⟨v₂, _, by rw [hu₂, hu₁], ?_,
        Exec.cast (Exec.seq (Exec.cond_true hsym' he₁) he₂) rfl ?_⟩
      · simp [Function.update_of_ne, *, Ne.symm]; omega
      · congr 2
        dsimp only
        rw [Function.update_of_ne ‹c ≠ s›.symm, hs, binSyms_shift]
        simp
  | false =>
      have he₁ := Exec.act (body := body) (.done : Act T Q A U) (mk v S)
      rw [run_done] at he₁
      obtain ⟨v₂, hu₂, he₂⟩ := bshift_exec body ‹s ≠ tx› (fun _ => bitSymbol false) v S htx
      refine ⟨v₂, _, hu₂, ?_,
        Exec.cast (Exec.seq (Exec.cond_false (p := baddTo c s tx ty tz cy) hsym' he₁) he₂) rfl ?_⟩
      · rw [hs]; simp; omega
      · congr 2
        rw [hs, binSyms_shift]
        simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero, ← hc, Function.update_eq_self]

/-- Schoolbook multiplication into the empty `c`. -/
def bmul (a b c s t tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (bcopy b s tx ty)
    (.seq (bpad s a tx ty)
      (.seq (bzero s c tx)
        (.seq (eachSym a t (mulIter c s tx ty tz cy))
          (.seq (moveR t a id) (bclear s)))))

/-- `bmul`: `a` holding `binSyms La x` and `b` holding `binSyms Lb y` (`x < 2 ^ La`,
`y < 2 ^ Lb`); the empty `c` ends holding `binSyms (La + Lb) (x * y)`, every other register as
it started, in at most `La (12 (La + Lb) + 20) + 16 (La + Lb) + 24` steps. Scan slot `cy`
(outside `c`, `s`) carries the additions; the scan slots `c`, `s` are scratch. -/
theorem bmul_exec {a b c s t tx ty tz cy : Fin T} (hreg : [a, b, c, s, t, tx, ty, tz].Nodup)
    (hcc : cy ≠ c) (hcs : cy ≠ s) {La Lb x y : ℕ} (hx : x < 2 ^ La) (hy : y < 2 ^ Lb)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms La x) (hb : S.R b = binSyms Lb y)
    (hc : S.R c = []) (hs : S.R s = []) (ht : S.R t = []) (htx : S.R tx = [])
    (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ La * (12 * (La + Lb) + 20) + 16 * (La + Lb) + 24 ∧
      Exec body (bmul a b c s t tx ty tz cy) (mk v S) m
        (mk v' { S with R := Function.update S.R c (binSyms (La + Lb) (x * y)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  set W := Lb + La with hW
  -- `s := b`
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body (a := b) (c := s) (t₁ := tx) (t₂ := ty) (by regs_nodup)
    v S htx hty
  set R₁ := Function.update S.R s (S.R b ++ S.R s) with hR₁
  -- pad `s` with `La` high zeros
  obtain ⟨v₂, hu₂, he₂⟩ := bpad_exec body (a := s) (eR := a) (t₁ := tx) (t₂ := ty) (by regs_nodup)
    hy v₁ { S with R := R₁ } (by simp [hR₁, hb, hs]) (by simp [Function.update_of_ne, *, Ne.symm])
    (by simp [Function.update_of_ne, *, Ne.symm])
  have hR₁a : R₁ a = binSyms La x := by simp [Function.update_of_ne, *]
  dsimp only at he₂
  rw [hR₁a, length_binSyms] at he₂
  set R₂ := Function.update R₁ s (binSyms W y) with hR₂
  -- `c := W` zeros
  obtain ⟨v₃, hu₃, he₃⟩ := bzero_exec body (wR := s) (c := c) (t := tx) (by regs_nodup) v₂
    { S with R := R₂ } (by simp [Function.update_of_ne, *, Ne.symm])
  have hR₂s : R₂ s = binSyms W y := by simp [hR₂]
  have hR₂c : R₂ c = [] := by simp [Function.update_of_ne, *]
  dsimp only at he₃
  rw [hR₂s, length_binSyms, hR₂c, List.append_nil] at he₃
  set R₃ := Function.update R₂ c (binSyms W 0) with hR₃
  -- the loop over the bits of `a`
  let Ψ : ℕ → Regs T A := fun j =>
    Function.update (Function.update R₃ c (binSyms W (y * (x % 2 ^ j)))) s (binSyms W (2 ^ j * y))
  have hR₃a : R₃ a = binSyms La x := by
    simp [Function.update_of_ne, *]
  have hp : SymSpec body (mulIter c s tx ty tz cy) a t (R₃ a) Ψ (12 * W + 17) := by
    intro j hj w S' hsym hS'
    rw [hR₃a, length_binSyms] at hj
    have hbit : (R₃ a)[j] = bitSymbol (x.testBit j) := by
      simp only [hR₃a, getElem_binSyms]
    have hpow : 2 ^ j * 2 ^ Lb ≤ 2 ^ W := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm : x % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    obtain ⟨w', m, hw', hm', he⟩ := mulIter_exec body (c := c) (s := s) (tx := tx) (ty := ty)
      (tz := tz) (by regs_nodup) hcc hcs (W := W) (u := y * (x % 2 ^ j)) (w := 2 ^ j * y)
      (lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hy hm) (by rw [Nat.mul_comm]; exact hpow))
      (lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hy (Nat.two_pow_pos j)) hpow)
      (x.testBit j) w S' (by rw [hsym, hbit])
      (by rw [hS' c ‹a ≠ c›.symm ‹c ≠ t›]; simp [Ψ, Function.update_of_ne, *])
      (by rw [hS' s ‹a ≠ s›.symm ‹s ≠ t›]; simp [Ψ])
      (by rw [hS' tx ‹a ≠ tx›.symm ‹t ≠ tx›.symm]
          simp [Ψ, Function.update_of_ne, *, Ne.symm])
      (by rw [hS' ty ‹a ≠ ty›.symm ‹t ≠ ty›.symm]
          simp [Ψ, Function.update_of_ne, *, Ne.symm])
      (by rw [hS' tz ‹a ≠ tz›.symm ‹t ≠ tz›.symm]
          simp [Ψ, Function.update_of_ne, *, Ne.symm])
    refine ⟨w', _, m, hw', hm', he, by simp [Function.update_of_ne, *],
      by simp [Function.update_of_ne, *, Ne.symm], fun k hka hkt => ?_⟩
    have hval : y * (x % 2 ^ j) + (x.testBit j).toNat * (2 ^ j * y) = y * (x % 2 ^ (j + 1)) := by
      rw [mod_two_pow_succ_testBit]; ring
    rw [hval, show 2 * (2 ^ j * y) = 2 ^ (j + 1) * y by ring]
    by_cases hkc : k = c
    · subst hkc; simp [Ψ, Function.update_of_ne, *]
    by_cases hks : k = s
    · subst hks; simp [Ψ]
    simp only [Function.update_of_ne hkc, Function.update_of_ne hks, hS' k hka hkt, Ψ]
  obtain ⟨v₄, R₄, m₄, hu₄, hm₄, he₄, ha₄, ht₄, hΨ₄⟩ := eachSym_exec body ‹a ≠ t› v₃
    { S with R := R₃ } hp (fun k _ _ => by
      simp only [Ψ, hR₃, hR₂, hR₁, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.one_mul,
        Function.update_apply]
      split_ifs <;> simp_all)
  dsimp only at hm₄ ht₄ hΨ₄
  rw [hR₃a, length_binSyms] at hm₄ hΨ₄
  rw [hR₃a] at ht₄
  -- restore `a` and clear `s`
  have hR₃t : R₃ t = [] := by simp [Function.update_of_ne, *, Ne.symm]
  rw [hR₃t, List.append_nil] at ht₄
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body t a ‹a ≠ t›.symm id v₄ { S with R := R₄ }
  obtain ⟨v₆, hu₆, -, he₆⟩ := bclear_exec body s v₅
    { S with R := movedR R₄ t a id (R₄ t) }
  have h4s : movedR R₄ t a id (R₄ t) s = binSyms W (2 ^ La * y) := by
    simp only [movedR, Function.update_of_ne ‹a ≠ s›.symm, Function.update_of_ne ‹s ≠ t›]
    rw [hΨ₄ s ‹a ≠ s›.symm ‹s ≠ t›]; simp [Ψ]
  refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))) rfl ?_⟩
  · dsimp only
    rw [h4s, ht₄, hb]
    simp only [length_binSyms, List.length_reverse]
    simp only [hW] at hm₄ ⊢
    nlinarith
  · congr 2
    have hmod : x % 2 ^ La = x := Nat.mod_eq_of_lt hx
    funext k
    dsimp only
    by_cases hks : k = s
    · subst hks; simp [Function.update_of_ne, *, Ne.symm]
    rw [Function.update_of_ne hks]
    by_cases hka : k = a
    · subst hka; simp [movedR, Function.update_of_ne, *]
    by_cases hkt : k = t
    · subst hkt; simp [movedR, Function.update_of_ne, *, Ne.symm]
    simp only [movedR, Function.update_of_ne hka, Function.update_of_ne hkt]
    rw [hΨ₄ k hka hkt]
    by_cases hkc : k = c
    · subst hkc
      simp [Ψ, Function.update_of_ne, *, Nat.mul_comm, Nat.add_comm]
    simp [Ψ, Function.update_of_ne, *]

end IntegerMultBounds.MathlibTM2.Host
