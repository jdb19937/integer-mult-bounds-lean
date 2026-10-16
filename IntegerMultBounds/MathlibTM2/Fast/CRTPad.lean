module

public import IntegerMultBounds.MathlibTM2.Fast.CRTBase
public import IntegerMultBounds.MathlibTM2.Fast.CRTBox

/-!
# The address loop and the padding scans of the CRT layout

**Address loop.** `crtAL L V I` runs, for every field index `F < 2 ^ W` with `W = crtPre a m`
(one iteration per symbol of the count register `L.nF`, which holds `2 ^ W` symbols), a code
pass of the validity automaton `crtVA` over the index register `L.fc` (holding
`binSyms W F`), the packed bounds `L.sg` (`binSyms W (crtSig a s m)`) and the field-end mask
`L.mq` (`binSyms W (crtMask a m)`); then `V` if `F` is valid (`crtVal a s m F`) and `I`
otherwise; then increments `L.fc`. `crtAL_runs`: given iteration contracts of `V` and `I` off
the loop registers (`crtALProt`), the other registers go from `Ψ 0` to `Ψ (2 ^ W)` in at most
`2 ^ W (b + 10 W + 13) + 2 · 2 ^ W + 4` steps.

**Padding scan.** `crtPadP` copies one record of `B` symbols (`B = |bU|`) from the coefficient
stream onto the accumulator at a valid index and a copy of the zero record `z` (register `zr`)
at an invalid one; the accumulator holds the reversed output, and a final move puts it on the
destination. `crtPad_runs`: for the coefficient records `l` (`l.length = crtProd s d`, all of
length `B`) the destination gains the box of `crtPadC l z` (the record `l[k]` at the valid
coordinates of mixed-radix value `k`, `z` elsewhere) along `crtRevAx d`.

**Deletion scan.** `crtDelP` moves the record at a valid index onto the accumulator and drops
the record at an invalid one. `crtDel_runs`: the destination gains the records at the valid
indices, in increasing order.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult

set_option linter.unusedSimpArgs false

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-! ### The address loop -/

/-- The registers of the address loop: count `nF` with its spare `tN`; index `fc`, packed bounds
`sg`, mask `mq` (the code-pass inputs) with spares `c0 c1 c2`; increment spare `it`; scan slots
`st` (automaton state) and `cy` (carry). -/
structure CrtAL (T : ℕ) where
  nF : Fin T
  tN : Fin T
  fc : Fin T
  sg : Fin T
  mq : Fin T
  c0 : Fin T
  c1 : Fin T
  c2 : Fin T
  it : Fin T
  st : Fin T
  cy : Fin T

namespace CrtAL

variable (L : CrtAL T)

/-- The registers that the iteration bodies must keep. -/
def Prot (k : Fin T) : Prop :=
  k = L.nF ∨ k = L.tN ∨ k = L.fc ∨ k = L.sg ∨ k = L.mq ∨ k = L.c0 ∨ k = L.c1 ∨ k = L.c2 ∨ k = L.it

instance (k : Fin T) : Decidable (L.Prot k) := by unfold Prot; infer_instance

/-- Distinct registers. -/
def Ok : Prop := [L.nF, L.tN, L.fc, L.sg, L.mq, L.c0, L.c1, L.c2, L.it, L.st].Nodup

/-- The register file during iteration `j`: index `j`, the bounds and mask, empty spares, and
`R` elsewhere. -/
def regs (W σ μ : ℕ) (R : Regs T A) (j : ℕ) : Regs T A := fun k =>
  if k = L.fc then binSyms W j else if k = L.sg then binSyms W σ else if k = L.mq then binSyms W μ
  else if k = L.c0 ∨ k = L.c1 ∨ k = L.c2 ∨ k = L.it then [] else R k

end CrtAL

/-- One iteration: validity code pass, `V` or `I`, increment of the index. -/
def crtALBody (L : CrtAL T) (V I : Pr P T Q A U) : Pr P T Q A U :=
  .seq (codePass ![L.fc, L.sg, L.mq] ![L.c0, L.c1, L.c2] L.st (crtVA A))
    (.seq (.cond (fun v => decide ((crtVA A).out (v.scan L.st) = 1)) V I)
      (.seq (.act (setCarry L.cy)) (incrField L.fc L.it L.cy)))

/-- The address loop: one iteration per symbol of `L.nF`. -/
def crtAL (L : CrtAL T) (V I : Pr P T Q A U) : Pr P T Q A U :=
  crtFor L.nF L.tN (crtALBody L V I)

lemma crt_inj3 {x y z : Fin T} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) :
    Function.Injective ![x, y, z] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

section Loop

variable {d : ℕ} (a s : Fin d → ℕ)

theorem crtALBody_iter (L : CrtAL T) (hL : L.Ok) {m : ℕ} (hm : m ≤ d)
    (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j) {V I : Pr P T Q A U} {Ψ : ℕ → Regs T A} {b : ℕ}
    (hV : ∀ F < 2 ^ crtPre a m, crtVal a s m F = true → ∀ R : Regs T A,
      (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      crtRuns body V R (fun k => if L.Prot k then R k else Ψ (F + 1) k) b)
    (hI : ∀ F < 2 ^ crtPre a m, crtVal a s m F = false → ∀ R : Regs T A,
      (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      crtRuns body I R (fun k => if L.Prot k then R k else Ψ (F + 1) k) b) :
    crtIter (body := body) (crtALBody L V I) L.nF L.tN
      (fun j => L.regs (crtPre a m) (crtSig a s m) (crtMask a m) (Ψ j) j)
      (b + 10 * crtPre a m + 10) (2 ^ crtPre a m) := by
  intro F hF R hR
  have hL' := hL
  unfold CrtAL.Ok at hL'
  regs_ne hL'
  set W := crtPre a m with hW
  set σ := crtSig a s m with hσ
  set μ := crtMask a m with hμ
  intro v S hS hLe
  -- the code pass
  have hfc : S.R L.fc = binSyms W F := by
    rw [hS, hR _ (Ne.symm ‹L.nF ≠ L.fc›) (Ne.symm ‹L.tN ≠ L.fc›)]; simp [CrtAL.regs]
  have hsg : S.R L.sg = binSyms W σ := by
    rw [hS, hR _ (Ne.symm ‹L.nF ≠ L.sg›) (Ne.symm ‹L.tN ≠ L.sg›)]
    simp [CrtAL.regs, ‹L.fc ≠ L.sg›.symm]
  have hmk : S.R L.mq = binSyms W μ := by
    rw [hS, hR _ (Ne.symm ‹L.nF ≠ L.mq›) (Ne.symm ‹L.tN ≠ L.mq›)]
    simp [CrtAL.regs, ‹L.fc ≠ L.mq›.symm, ‹L.sg ≠ L.mq›.symm]
  have hc : ∀ k, k = L.c0 ∨ k = L.c1 ∨ k = L.c2 ∨ k = L.it → S.R k = [] := by
    intro k hk
    have h1 : k ≠ L.nF := by rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by assumption)
    have h2 : k ≠ L.tN := by rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by assumption)
    have h3 : k ≠ L.fc := by rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by assumption)
    have h4 : k ≠ L.sg := by rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by assumption)
    have h5 : k ≠ L.mq := by rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by assumption)
    rw [hS, hR _ h1 h2]; simp [CrtAL.regs, h3, h4, h5, hk]
  have hCL : CodeLayout ![L.fc, L.sg, L.mq] ![L.c0, L.c1, L.c2] L.st := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact crt_inj3 ‹_› ‹_› ‹_›
    · exact crt_inj3 ‹_› ‹_› ‹_›
    · intro i j; fin_cases i <;> fin_cases j <;> simp <;> assumption
    · intro i; fin_cases i <;> simp <;> assumption
    · intro i; fin_cases i <;> simp <;> assumption
  obtain ⟨v₁, hu₁, hst₁, he₁⟩ := codePass_exec body hCL (crtVA A) W ![F, σ, μ] v S
    (fun r => by fin_cases r <;> simp [hfc, hsg, hmk])
    (fun r => by fin_cases r <;> simp [hc])
  have hσW : σ < 2 ^ W := crtSig_lt a s (fun j => (hs j).2) m hm
  have ha : ∀ j, 1 ≤ a j := fun j => by
    by_contra hz
    have h0 : a j = 0 := by omega
    have := hs j; rw [h0] at this; omega
  have hμW : μ < 2 ^ W := crtMask_lt a ha m hm
  have hrun := crtVA_run (A := A) a s hs m hm ![F, σ, μ] true
    (by simp only [Matrix.cons_val_one, Matrix.head_cons]; exact Nat.mod_eq_of_lt hσW)
    (by simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        exact Nat.mod_eq_of_lt hμW)
  simp only [Bool.true_and, Matrix.cons_val_zero] at hrun
  have hout : (crtVA A).out (v₁.scan L.st) = if crtVal a s m F then 1 else 0 := by
    rw [hst₁]; exact (congrArg (crtVA A).out hrun).trans (crtVA_out _ _)
  -- the body proper
  have hagree : ∀ k, ¬ L.Prot k → R k = Ψ F k := by
    intro k hk
    simp only [CrtAL.Prot, not_or] at hk
    rw [hR k hk.1 hk.2.1]
    simp [CrtAL.regs, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1, hk.2.2.2.2.2.2.1,
      hk.2.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.2]
  have hbody : ∃ (v₂ : HS T Q A U) (m₂ : ℕ), v₂.user = v₁.user ∧ m₂ ≤ b ∧
      Exec body (.cond (fun v => decide ((crtVA A).out (v.scan L.st) = 1)) V I) (mk v₁ S)
        (m₂ + 1) (mk v₂ { S with R := fun k => if L.Prot k then R k else Ψ (F + 1) k }) := by
    by_cases hv : crtVal a s m F = true
    · obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hV F hF hv R hagree v₁ S hS hLe
      refine ⟨v₂, m₂, hu₂, hm₂, Exec.cond_true ?_ he₂⟩
      simp [hout, hv]
    · have hv' : crtVal a s m F = false := by simpa using hv
      obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hI F hF hv' R hagree v₁ S hS hLe
      refine ⟨v₂, m₂, hu₂, hm₂, Exec.cond_false ?_ he₂⟩
      simp [hout, hv']
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hbody
  -- the increment
  set R₂ : Regs T A := fun k => if L.Prot k then R k else Ψ (F + 1) k with hR₂
  have hR₂fc : R₂ L.fc = (binBits W F).map bitSymbol := by
    simp [hR₂, CrtAL.Prot, ← hS, hfc, binSyms_eq]
  have hR₂it : R₂ L.it = [] := by
    simp [hR₂, CrtAL.Prot, ← hS]; exact hc _ (by simp)
  have he₃ := Exec.act (body := body) (setCarry L.cy) (mk v₂ { S with R := R₂ })
  set v₃ : HS T Q A U := { v₂ with scan := Function.update v₂.scan L.cy (bitSymbol true) }
  have hrun₃ : (setCarry L.cy : Act T Q A U).run (mk v₂ { S with R := R₂ }) =
      mk v₃ { S with R := R₂ } := rfl
  rw [hrun₃] at he₃
  obtain ⟨v₄, hu₄, _, he₄⟩ := incrField_exec body L.fc L.it L.cy ‹L.fc ≠ L.it› (binBits W F) true
    v₃ { S with R := R₂ } hR₂fc hR₂it (by simp [v₃])
  rw [incBits_binBits] at he₄
  refine ⟨v₄, (6 * W + 4) + ((m₂ + 1) + (1 + (4 * W + 4))), ?_, ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.cast he₄ (by simp) ?_)))⟩
  · rw [hu₄]; simp [v₃, hu₂, hu₁]
  · omega
  · congr 2
    funext k
    by_cases hk : k = L.fc
    · subst hk
      simp [hR₂, CrtAL.regs, binSyms_eq, ‹L.nF ≠ L.fc›.symm, ‹L.tN ≠ L.fc›.symm]
    · simp only [Function.update_of_ne hk, hR₂]
      by_cases hp : L.Prot k
      · simp only [hp, ↓reduceIte]
        by_cases hk' : k = L.nF ∨ k = L.tN
        · simp [hk']
        · simp only [hk', ↓reduceIte]
          rw [hR k (fun h => hk' (Or.inl h)) (fun h => hk' (Or.inr h))]
          simp only [CrtAL.regs, hk, ↓reduceIte]
          split_ifs with h1 h2 h3 <;> try rfl
          exfalso
          simp only [CrtAL.Prot] at hp
          rcases hp with h | h | h | h | h | h | h | h | h
          exacts [hk' (Or.inl h), hk' (Or.inr h), hk h, h1 h, h2 h, h3 (Or.inl h),
            h3 (Or.inr (Or.inl h)), h3 (Or.inr (Or.inr (Or.inl h))), h3 (Or.inr (Or.inr (Or.inr h)))]
      · have hk' : ¬ (k = L.nF ∨ k = L.tN) := by
          simp only [CrtAL.Prot, not_or] at hp; simp [hp.1, hp.2.1]
        simp only [hp, hk', ↓reduceIte]
        simp only [CrtAL.Prot, not_or] at hp
        simp [CrtAL.regs, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
          hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2]

/-- The address loop over the `2 ^ crtPre a m` field indices. -/
theorem crtAL_runs (L : CrtAL T) (hL : L.Ok) {m : ℕ} (hm : m ≤ d)
    (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j) {V I : Pr P T Q A U} {Ψ : ℕ → Regs T A} {b : ℕ}
    (hV : ∀ F < 2 ^ crtPre a m, crtVal a s m F = true → ∀ R : Regs T A,
      (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      crtRuns body V R (fun k => if L.Prot k then R k else Ψ (F + 1) k) b)
    (hI : ∀ F < 2 ^ crtPre a m, crtVal a s m F = false → ∀ R : Regs T A,
      (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      crtRuns body I R (fun k => if L.Prot k then R k else Ψ (F + 1) k) b)
    (lN : List (Fin (A + 4))) (hlN : lN.length = 2 ^ crtPre a m) :
    crtRuns body (crtAL L V I)
      (crtForRegs L.nF L.tN (L.regs (crtPre a m) (crtSig a s m) (crtMask a m) (Ψ 0) 0) lN [])
      (crtForRegs L.nF L.tN (L.regs (crtPre a m) (crtSig a s m) (crtMask a m)
        (Ψ (2 ^ crtPre a m)) 0) lN [])
      (2 ^ crtPre a m * (b + 10 * crtPre a m + 13) + 2 * 2 ^ crtPre a m + 4) := by
  have hL' := hL
  unfold CrtAL.Ok at hL'
  regs_ne hL'
  have h := crtFor_runs (body := body) ‹L.nF ≠ L.tN›
    (crtALBody_iter a s L hL hm hs hV hI) lN hlN
  refine crtRuns_mono (crtRuns_congr h ?_) (by ring_nf; omega)
  funext k
  simp only [crtForRegs, CrtAL.regs]
  split_ifs <;> simp_all [binSyms_mod (A := A) (crtPre a m) (2 ^ crtPre a m) |>.symm.trans
    (by rw [Nat.mod_self])]

/-- The address loop with its setup (index `0`, count `2 ^ W`) and cleanup. -/
def crtALFull (L : CrtAL T) (V I : Pr P T Q A U) : Pr P T Q A U :=
  .seq (zeroBits L.mq L.fc L.c0)
    (.seq (crtPush L.nF tick)
      (.seq (upow2 L.mq L.nF L.c0 L.c1)
        (.seq (crtAL L V I) (.seq (uclear L.fc) (uclear L.nF)))))

/-- The address loop from a file `R₀` whose loop registers are empty except the bounds `L.sg`
and the mask `L.mq`: the other registers go from `Ψ 0 = R₀` to `Ψ (2 ^ W)`. -/
theorem crtALFull_runs (L : CrtAL T) (hL : L.Ok) {m : ℕ} (hm : m ≤ d)
    (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j) {V I : Pr P T Q A U} {Ψ : ℕ → Regs T A} {b : ℕ}
    (hV : ∀ F < 2 ^ crtPre a m, crtVal a s m F = true → ∀ R : Regs T A,
      (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      crtRuns body V R (fun k => if L.Prot k then R k else Ψ (F + 1) k) b)
    (hI : ∀ F < 2 ^ crtPre a m, crtVal a s m F = false → ∀ R : Regs T A,
      (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      crtRuns body I R (fun k => if L.Prot k then R k else Ψ (F + 1) k) b)
    (R₀ : Regs T A) (h₀ : ∀ k, ¬ L.Prot k → R₀ k = Ψ 0 k)
    (hnF : R₀ L.nF = []) (htN : R₀ L.tN = []) (hfc : R₀ L.fc = [])
    (hsg : R₀ L.sg = binSyms (crtPre a m) (crtSig a s m))
    (hmq : R₀ L.mq = binSyms (crtPre a m) (crtMask a m))
    (hc0 : R₀ L.c0 = []) (hc1 : R₀ L.c1 = []) (hc2 : R₀ L.c2 = []) (hit : R₀ L.it = []) :
    crtRuns body (crtALFull L V I) R₀ (fun k => if L.Prot k then R₀ k else Ψ (2 ^ crtPre a m) k)
      (2 ^ crtPre a m * (b + 10 * crtPre a m + 21) + 25 * crtPre a m + 21) := by
  have hL' := hL
  unfold CrtAL.Ok at hL'
  regs_ne hL'
  set W := crtPre a m with hW
  set N := 2 ^ W with hN
  -- setup
  have h₁ := crtZeroBits_runs (body := body) (Ne.symm ‹L.fc ≠ L.mq›) ‹L.mq ≠ L.c0›
    ‹L.fc ≠ L.c0› R₀ hc0
  set R₁ := Function.update R₀ L.fc (binSyms (R₀ L.mq).length 0 ++ R₀ L.fc) with hR₁
  have h₂ := crtPush_runs (body := body) L.nF tick R₁
  set R₂ := Function.update R₁ L.nF (tick :: R₁ L.nF) with hR₂
  have h₃ := crtUpow2_runs (body := body) (a := L.mq) (b := L.nF) (t₁ := L.c0) (t₂ := L.c1)
    (by regs_nodup) R₂ (by simp [hR₂, hR₁, *, Ne.symm]) (by simp [hR₂, hR₁, *, Ne.symm])
  set R₃ := Function.update R₂ L.nF ((R₂ L.nF).flatMap (List.replicate (2 ^ (R₂ L.mq).length)))
    with hR₃
  have hmqlen : (R₀ L.mq).length = W := by rw [hmq, length_binSyms]
  have hR₃' : R₃ = crtForRegs L.nF L.tN (L.regs W (crtSig a s m) (crtMask a m) (Ψ 0) 0)
      (List.replicate N tick) [] := by
    funext k
    simp only [hR₃, hR₂, hR₁, crtForRegs, CrtAL.regs]
    by_cases k1 : k = L.nF
    · subst k1
      have e1 : (Function.update (Function.update R₀ L.fc (binSyms (R₀ L.mq).length 0 ++ R₀ L.fc))
          L.nF (tick :: Function.update R₀ L.fc (binSyms (R₀ L.mq).length 0 ++ R₀ L.fc) L.nF)
          L.mq).length = W := by
        rw [Function.update_of_ne (Ne.symm ‹L.nF ≠ L.mq›),
          Function.update_of_ne (Ne.symm ‹L.fc ≠ L.mq›), hmqlen]
      rw [e1]
      simp [Function.update_of_ne ‹L.nF ≠ L.fc›, hnF, hN]
    · rw [Function.update_of_ne k1, Function.update_of_ne k1]
      by_cases k2 : k = L.tN
      · subst k2; simp [k1, Function.update_of_ne ‹L.tN ≠ L.fc›, htN]
      · by_cases k3 : k = L.fc
        · subst k3; simp [k1, k2, hfc, hmqlen]
        · rw [Function.update_of_ne k3]
          by_cases k4 : k = L.sg
          · subst k4; simp [k1, k2, k3, hsg]
          · by_cases k5 : k = L.mq
            · subst k5; simp [k1, k2, k3, k4, hmq]
            · by_cases k6 : k = L.c0 ∨ k = L.c1 ∨ k = L.c2 ∨ k = L.it
              · simp only [k1, k2, k3, k4, k5, k6, ↓reduceIte]
                rcases k6 with rfl | rfl | rfl | rfl <;> assumption
              · simp only [k1, k2, k3, k4, k5, k6, ↓reduceIte]
                apply h₀
                simp only [CrtAL.Prot, not_or] at k6 ⊢; exact ⟨k1, k2, k3, k4, k5, k6⟩
  rw [hR₃'] at h₃
  -- the loop
  have h₄ := crtAL_runs a s L hL hm hs hV hI (List.replicate N tick) (by simp [hN, hW])
  -- cleanup
  set R₄ := crtForRegs L.nF L.tN (L.regs W (crtSig a s m) (crtMask a m) (Ψ N) 0)
    (List.replicate N tick) [] with hR₄
  have h₅ := crtClear_runs (body := body) L.fc R₄
  have h₆ := crtClear_runs (body := body) L.nF (Function.update R₄ L.fc [])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃
    (crtRuns_seq h₄ (crtRuns_seq h₅ h₆))))) ?_) ?_
  · funext k
    by_cases k1 : k = L.nF
    · subst k1; simp [CrtAL.Prot, hnF]
    · rw [Function.update_of_ne k1]
      by_cases k3 : k = L.fc
      · subst k3; simp [CrtAL.Prot, hfc]
      · rw [Function.update_of_ne k3]
        simp only [hR₄, crtForRegs, CrtAL.regs, k1, k3, ↓reduceIte]
        by_cases k2 : k = L.tN
        · subst k2; simp [CrtAL.Prot, htN]
        · simp only [k2, ↓reduceIte]
          by_cases k4 : k = L.sg
          · subst k4; simp [CrtAL.Prot, hsg]
          · simp only [k4, ↓reduceIte]
            by_cases k5 : k = L.mq
            · subst k5; simp [CrtAL.Prot, hmq]
            · simp only [k5, ↓reduceIte]
              by_cases k6 : k = L.c0 ∨ k = L.c1 ∨ k = L.c2 ∨ k = L.it
              · have hp : L.Prot k := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr k6))))
                simp only [k6, hp, ↓reduceIte]
                rcases k6 with rfl | rfl | rfl | rfl
                · exact hc0.symm
                · exact hc1.symm
                · exact hc2.symm
                · exact hit.symm
              · have hp : ¬ L.Prot k := by
                  simp only [CrtAL.Prot, not_or] at k6 ⊢; exact ⟨k1, k2, k3, k4, k5, k6⟩
                simp [k6, hp]
  · have l1 : (R₂ L.mq).length = W := by
      rw [hR₂, Function.update_of_ne (Ne.symm ‹L.nF ≠ L.mq›), hR₁,
        Function.update_of_ne (Ne.symm ‹L.fc ≠ L.mq›), hmqlen]
    have l2 : (R₂ L.nF).length = 1 := by
      rw [hR₂, Function.update_self, hR₁, Function.update_of_ne ‹L.nF ≠ L.fc›, hnF]; rfl
    have l3 : (R₄ L.fc).length = W := by
      simp [hR₄, crtForRegs, CrtAL.regs, Ne.symm ‹L.nF ≠ L.fc›, Ne.symm ‹L.tN ≠ L.fc›]
    have l4 : (Function.update R₄ L.fc [] L.nF).length = N := by
      rw [Function.update_of_ne ‹L.nF ≠ L.fc›]; simp [hR₄, crtForRegs]
    rw [hmqlen, l1, l2, l3, l4]
    nlinarith

end Loop

/-! ### Records on a stream -/

section Records

variable {α : Type*}

/-- The first `B` symbols of a flattened record list starting at record `c` form record `c`. -/
lemma crt_drop_flatten (l : List (List α)) (c : ℕ) (hc : c < l.length) :
    (l.drop c).flatten = l[c] ++ (l.drop (c + 1)).flatten := by
  rw [List.drop_eq_getElem_cons hc, List.flatten_cons]

lemma crt_take_drop_flatten (l : List (List α)) (B : ℕ) (hB : ∀ x ∈ l, x.length = B) (c : ℕ)
    (hc : c < l.length) :
    ((l.drop c).flatten).take B = l[c] ∧ ((l.drop c).flatten).drop B = (l.drop (c + 1)).flatten := by
  rw [crt_drop_flatten l c hc]
  have hlen : l[c].length = B := hB _ (List.getElem_mem hc)
  constructor
  · rw [List.take_append_of_le_length (by omega), ← hlen, List.take_length]
  · rw [List.drop_append_of_le_length (by omega), ← hlen, List.drop_length, List.nil_append]

lemma crt_length_drop_flatten (l : List (List α)) (B : ℕ) (hB : ∀ x ∈ l, x.length = B) (c : ℕ) :
    ((l.drop c).flatten).length = (l.length - c) * B := by
  rw [List.length_flatten]
  have : ∀ x ∈ (l.drop c), x.length = B := fun x hx => hB x (List.mem_of_mem_drop hx)
  rw [List.map_congr_left this, List.map_const', List.sum_replicate, List.length_drop,
    smul_eq_mul]

end Records

/-! ### Counting monotonicity -/

lemma crtCnt_mono {d : ℕ} (a s : Fin d → ℕ) (m : ℕ) {F F' : ℕ} (h : F ≤ F') :
    crtCnt a s m F ≤ crtCnt a s m F' := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  induction e with
  | zero => simp
  | succ e ih => rw [← Nat.add_assoc, crtCnt_succ_arg]; omega

/-! ### The padding scan -/

section Pad

variable {d : ℕ} (a s : Fin d → ℕ)

/-- The content of the padded box: the record `l[k]` at the valid coordinates of mixed-radix
value `k = ∑ j, x j · prefixProd s j`, and `z` at the invalid ones. -/
def crtPadC {α : Type*} (l : List α) (z : α) (x : Fin d → ℕ) : α :=
  if ∀ j, x j < s j then l.getD (∑ j, x j * prefixProd s j) z else z

/-- The padded records after the first `F` indices. -/
def crtPadRecs {α : Type*} (l : List α) (z : α) (F : ℕ) : List α :=
  (List.range F).map fun n => if crtVal a s d n then l.getD (crtCnt a s d n) z else z

lemma crtPadRecs_succ {α : Type*} (l : List α) (z : α) (F : ℕ) :
    crtPadRecs a s l z (F + 1) = crtPadRecs a s l z F ++
      [if crtVal a s d F then l.getD (crtCnt a s d F) z else z] := by
  simp [crtPadRecs, List.range_succ]

/-- The coordinates of an index along `crtRevAx d` are its digits. -/
lemma crtDec_revAx_full {n : ℕ} (hn : n < 2 ^ crtPre a d) :
    crtDec a (crtRevAx d) n 0 = fun j => crtDig a j n := by
  rw [crtDec_revAx a d le_rfl n hn]
  funext j; simp [j.isLt]

/-- After all indices, the padded records form the box of `crtPadC` along `crtRevAx d`. -/
theorem crtPadRecs_top {α : Type*} (hs : ∀ j, s j ≤ 2 ^ a j) (l : List α) (z : α) :
    crtPadRecs a s l z (2 ^ crtPre a d) = crtBox a (crtRevAx d) (crtPadC s l z) 0 := by
  rw [crtPadRecs, crtBox, crtW_revAx a d le_rfl]
  refine List.map_congr_left fun n hn => ?_
  have hn' := List.mem_range.1 hn
  rw [crtDec_revAx_full a hn', crtPadC]
  have hv : (∀ j, crtDig a j n < s j) ↔ crtVal a s d n = true := by
    simp only [crtVal, decide_eq_true_eq]
    exact ⟨fun H j _ => H j, fun H j => H j j.isLt⟩
  by_cases h : crtVal a s d n = true
  · rw [ite_eq_left h, ite_eq_left (hv.2 h), (crtCnt_main a s hs d le_rfl).2 n hn' h, crtK]
    congr 1
    rw [crtLow_of_le le_rfl]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hv.1 h'))]

lemma CrtAL.ne_of_not_prot {L : CrtAL T} {k : Fin T} (h : ¬ L.Prot k) :
    k ≠ L.nF ∧ k ≠ L.tN ∧ k ≠ L.fc ∧ k ≠ L.sg ∧ k ≠ L.mq ∧ k ≠ L.c0 ∧ k ≠ L.c1 ∧ k ≠ L.c2 ∧
      k ≠ L.it := by
  simp only [CrtAL.Prot, not_or] at h
  exact h

/-- The padding scan: one record of the coefficient stream `str` per valid index and a copy of
the zero record `zr` per invalid index onto the accumulator `acc` (reversed), then back onto
`str`. `bU` holds `B` ticks during the scan; `tA`, `tB`, `u` are spares. -/
def crtPadP (L : CrtAL T) (str acc zr bU tA tB u : Fin T) : Pr P T Q A U :=
  .seq (ucopy zr bU tA)
    (.seq (crtALFull L (crtCMv bU tA str acc) (.seq (crtCpy bU tA zr tB u) (crtMv tB acc)))
      (.seq (uclear bU) (crtMv acc str)))

/-- The padding scan: the coefficient records `l` on `str` (`crtProd s d` records of `B`
symbols) become the records of the box of `crtPadC s l z` along `crtRevAx d`. -/
theorem crtPad_runs (L : CrtAL T) (hL : L.Ok) {str acc zr bU tA tB u : Fin T}
    (hreg : [str, acc, zr, bU, tA, tB, u].Nodup)
    (hp : ∀ k ∈ [str, acc, zr, bU, tA, tB, u], ¬ L.Prot k)
    (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (l : List (List (Fin (A + 4)))) (z : List (Fin (A + 4))) (B : ℕ)
    (hl : l.length = crtProd s d) (hlB : ∀ x ∈ l, x.length = B) (hz : z.length = B)
    (R₀ : Regs T A) (hstr : R₀ str = l.flatten) (hzr : R₀ zr = z)
    (hacc : R₀ acc = []) (hbU : R₀ bU = []) (htA : R₀ tA = []) (htB : R₀ tB = [])
    (hu : R₀ u = [])
    (hnF : R₀ L.nF = []) (htN : R₀ L.tN = []) (hfc : R₀ L.fc = [])
    (hsg : R₀ L.sg = binSyms (crtPre a d) (crtSig a s d))
    (hmq : R₀ L.mq = binSyms (crtPre a d) (crtMask a d))
    (hc0 : R₀ L.c0 = []) (hc1 : R₀ L.c1 = []) (hc2 : R₀ L.c2 = []) (hit : R₀ L.it = []) :
    crtRuns body (crtPadP L str acc zr bU tA tB u) R₀
      (Function.update R₀ str (crtBox a (crtRevAx d) (crtPadC s l z) 0).flatten)
      (2 ^ crtPre a d * (10 * B + 10 * crtPre a d + 29) + 25 * crtPre a d + 6 * B + 29) := by
  have hreg' := hreg
  regs_ne hreg'
  have hsle : ∀ j, s j ≤ 2 ^ a j := fun j => (hs j).2.le
  set W := crtPre a d with hW
  set N := 2 ^ W with hN
  have pstr := hp str (by simp)
  have pacc := hp acc (by simp)
  have pbU := hp bU (by simp)
  have ptA := hp tA (by simp)
  -- `bU := B` ticks
  have h₁ := crtUcopy_runs (body := body) ‹zr ≠ bU› ‹zr ≠ tA› ‹bU ≠ tA› R₀ htA
  set R₁ := Function.update R₀ bU (List.replicate (R₀ zr).length tick ++ R₀ bU) with hR₁
  have hR₁bU : R₁ bU = List.replicate B tick := by simp [hR₁, hzr, hz, hbU]
  -- the loop invariant
  let Ψ : ℕ → Regs T A := fun F => Function.update (Function.update R₁ str
    ((l.drop (crtCnt a s d F)).flatten)) acc ((crtPadRecs a s l z F).flatten.reverse)
  have hΨstr : ∀ F, Ψ F str = (l.drop (crtCnt a s d F)).flatten := fun F => by
    simp [Ψ, Function.update_of_ne ‹str ≠ acc›]
  have hΨacc : ∀ F, Ψ F acc = (crtPadRecs a s l z F).flatten.reverse := fun F => by simp [Ψ]
  have hΨoth : ∀ F G k, k ≠ str → k ≠ acc → Ψ F k = Ψ G k := fun F G k h1 h2 => by
    simp [Ψ, Function.update_of_ne h1, Function.update_of_ne h2]
  have hcntlt : ∀ F < N, crtVal a s d F = true → crtCnt a s d F < l.length := by
    intro F hF hv
    have h1 : crtCnt a s d (F + 1) = crtCnt a s d F + 1 := by rw [crtCnt_succ_arg, hv]; rfl
    have h2 : crtCnt a s d (F + 1) ≤ crtCnt a s d N := crtCnt_mono a s d (by omega)
    have h3 : crtCnt a s d N = crtProd s d := (crtCnt_main a s hsle d le_rfl).1
    omega
  have hV : ∀ F < N, crtVal a s d F = true → ∀ R : Regs T A,
      (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      crtRuns body (crtCMv bU tA str acc) R (fun k => if L.Prot k then R k else Ψ (F + 1) k)
        (8 * B + 8) := by
    intro F hF hv R hR
    have hc := hcntlt F hF hv
    have hRstr : R str = (l.drop (crtCnt a s d F)).flatten := by rw [hR str pstr, hΨstr]
    have hRacc : R acc = (crtPadRecs a s l z F).flatten.reverse := by rw [hR acc pacc, hΨacc]
    have hRbU : R bU = List.replicate B tick := by
      rw [hR bU pbU, hΨoth F 0 bU ‹str ≠ bU›.symm ‹acc ≠ bU›.symm]
      simp [Ψ, Function.update_of_ne ‹str ≠ bU›.symm, Function.update_of_ne ‹acc ≠ bU›.symm,
        hR₁bU]
    have hRtA : R tA = [] := by
      rw [hR tA ptA]
      simp [Ψ, Function.update_of_ne ‹str ≠ tA›.symm, Function.update_of_ne ‹acc ≠ tA›.symm,
        hR₁, Function.update_of_ne ‹bU ≠ tA›.symm, htA]
    obtain ⟨htake, hdrop⟩ := crt_take_drop_flatten l B hlB (crtCnt a s d F) hc
    have hlen : (R bU).length ≤ (R str).length := by
      rw [hRbU, hRstr, crt_length_drop_flatten l B hlB, List.length_replicate]
      have : 1 ≤ l.length - crtCnt a s d F := by omega
      nlinarith
    have h := crtCMv_runs (body := body) (c := bU) (t := tA) (src := str) (dst := acc)
      (by regs_nodup) R hRtA hlen
    refine crtRuns_mono (crtRuns_congr h ?_) (by rw [hRbU, List.length_replicate]; omega)
    have hcs : crtCnt a s d (F + 1) = crtCnt a s d F + 1 := by rw [crtCnt_succ_arg, hv]; rfl
    funext k
    by_cases k1 : k = acc
    · rw [k1]
      simp only [Function.update_self, pacc, ↓reduceIte, hΨacc, crtPadRecs_succ, hv,
        List.flatten_append, List.reverse_append, hRbU, List.length_replicate, hRstr, htake,
        hRacc, List.getD_eq_getElem _ _ hc]
      simp
    · rw [Function.update_of_ne k1]
      by_cases k2 : k = str
      · rw [k2]
        simp only [Function.update_self, pstr, ↓reduceIte, hΨstr, hRbU, List.length_replicate,
          hRstr, hdrop, hcs]
      · rw [Function.update_of_ne k2]
        by_cases hk : L.Prot k
        · simp [hk]
        · simp only [hk, ↓reduceIte]
          rw [hR k hk, hΨoth F (F + 1) k k2 k1]
  have hI : ∀ F < N, crtVal a s d F = false → ∀ R : Regs T A,
      (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      crtRuns body (.seq (crtCpy bU tA zr tB u) (crtMv tB acc)) R
        (fun k => if L.Prot k then R k else Ψ (F + 1) k) (8 * B + 8) := by
    intro F hF hv R hR
    have pzr := hp zr (by simp)
    have ptB := hp tB (by simp)
    have pu := hp u (by simp)
    have hRoth : ∀ k, k ≠ str → k ≠ acc → ¬ L.Prot k → R k = R₁ k := fun k h1 h2 h3 => by
      rw [hR k h3]; simp [Ψ, Function.update_of_ne h1, Function.update_of_ne h2]
    have hRbU : R bU = List.replicate B tick := by
      rw [hRoth bU ‹str ≠ bU›.symm ‹acc ≠ bU›.symm pbU, hR₁bU]
    have hRtA : R tA = [] := by
      rw [hRoth tA ‹str ≠ tA›.symm ‹acc ≠ tA›.symm ptA, hR₁,
        Function.update_of_ne ‹bU ≠ tA›.symm, htA]
    have hRzr : R zr = z := by
      rw [hRoth zr ‹str ≠ zr›.symm ‹acc ≠ zr›.symm pzr, hR₁,
        Function.update_of_ne ‹zr ≠ bU›, hzr]
    have hRtB : R tB = [] := by
      rw [hRoth tB ‹str ≠ tB›.symm ‹acc ≠ tB›.symm ptB, hR₁,
        Function.update_of_ne ‹bU ≠ tB›.symm, htB]
    have hRu : R u = [] := by
      rw [hRoth u ‹str ≠ u›.symm ‹acc ≠ u›.symm pu, hR₁,
        Function.update_of_ne ‹bU ≠ u›.symm, hu]
    have h₁ := crtCpy_runs (body := body) (c := bU) (t := tA) (src := zr) (dst := tB) (u := u)
      (by regs_nodup) R hRtA hRu (by rw [hRbU, hRzr, List.length_replicate, hz])
    have h₂ := crtMv_runs (body := body) (Ne.symm ‹acc ≠ tB›)
      (Function.update R tB ((R zr).take (R bU).length ++ R tB))
    have hz' : (R zr).take (R bU).length = z := by
      rw [hRzr, hRbU, List.length_replicate, ← hz, List.take_length]
    refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ h₂) ?_)
      (by rw [Function.update_self, hz', hRtB, List.append_nil, hz, hRbU, List.length_replicate]
          omega)
    have hcs : crtCnt a s d (F + 1) = crtCnt a s d F := by rw [crtCnt_succ_arg, hv]; rfl
    funext k
    by_cases k1 : k = acc
    · rw [k1]
      simp only [Function.update_self, pacc, ↓reduceIte, hΨacc, crtPadRecs_succ, hv,
        Function.update_of_ne ‹acc ≠ tB›, hz', hRtB, List.append_nil, hR acc pacc]
      simp
    · rw [Function.update_of_ne k1]
      by_cases k2 : k = tB
      · rw [k2]
        simp [ptB, Ψ, Function.update_of_ne ‹str ≠ tB›.symm, Function.update_of_ne ‹acc ≠ tB›.symm,
          hR₁, Function.update_of_ne ‹bU ≠ tB›.symm, htB]
      · rw [Function.update_of_ne k2, Function.update_of_ne k2]
        by_cases hk : L.Prot k
        · simp [hk]
        · simp only [hk, ↓reduceIte]
          by_cases k3 : k = str
          · rw [k3, hR _ (k3 ▸ hk), hΨstr, hΨstr, hcs]
          · rw [hR k hk, hΨoth F (F + 1) k k3 k1]
  -- the loop
  have h₂ := crtALFull_runs a s L hL le_rfl hs hV hI R₁
    (fun k hk => by
      by_cases k1 : k = acc
      · rw [k1]; simp [Ψ, hR₁, Function.update_of_ne ‹acc ≠ bU›, hacc, crtPadRecs]
      · by_cases k2 : k = str
        · rw [k2]; simp [Ψ, Function.update_of_ne ‹str ≠ acc›, hR₁, Function.update_of_ne ‹str ≠ bU›, hstr, crtCnt]
        · simp [Ψ, Function.update_of_ne k1, Function.update_of_ne k2])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).1.symm, hnF, hW])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.1.symm, htN, hW])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.1.symm, hfc, hW])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.1.symm, hsg, hW])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.2.1.symm, hmq, hW])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.2.2.1.symm, hc0, hW])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.2.2.2.1.symm, hc1, hW])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.2.2.2.2.1.symm, hc2, hW])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.2.2.2.2.2.symm, hit, hW])
  set R₂ := fun k => if L.Prot k then R₁ k else Ψ N k with hR₂
  have h₃ := crtClear_runs (body := body) bU R₂
  have h₄ := crtMv_runs (body := body) ‹str ≠ acc›.symm (Function.update R₂ bU [])
  have hcN : crtCnt a s d N = l.length := by rw [(crtCnt_main a s hsle d le_rfl).1, hl]
  have hR₂str : R₂ str = [] := by simp [hR₂, pstr, hΨstr, hcN]
  have hR₂acc : R₂ acc = (crtPadRecs a s l z N).flatten.reverse := by simp [hR₂, pacc, hΨacc]
  have hR₂bU : R₂ bU = List.replicate B tick := by
    simp [hR₂, pbU, Ψ, Function.update_of_ne ‹str ≠ bU›.symm,
      Function.update_of_ne ‹acc ≠ bU›.symm, hR₁bU]
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ h₄)))
    ?_) ?_
  · funext k
    by_cases k1 : k = str
    · rw [k1]
      simp only [Function.update_self, Function.update_of_ne ‹str ≠ bU›, hR₂str, hR₂acc,
        Function.update_of_ne ‹acc ≠ bU›, Function.update_of_ne ‹str ≠ acc›, List.reverse_reverse,
        List.append_nil, hN, hW, crtPadRecs_top a s hsle]
    · rw [Function.update_of_ne k1, Function.update_of_ne k1]
      by_cases k2 : k = acc
      · rw [k2]; simp [hacc]
      · rw [Function.update_of_ne k2]
        by_cases k3 : k = bU
        · rw [k3]; simp [hbU]
        · rw [Function.update_of_ne k3]
          by_cases hk : L.Prot k
          · simp [hR₂, hk, hR₁, Function.update_of_ne k3]
          · simp [hR₂, hk, Ψ, Function.update_of_ne k1, Function.update_of_ne k2, hR₁,
              Function.update_of_ne k3]
  · have e1 : (R₀ zr).length = B := by rw [hzr, hz]
    have e2 : ((Function.update R₂ bU []) acc).length = N * B := by
      rw [Function.update_of_ne ‹acc ≠ bU›, hR₂acc, List.length_reverse, crtPadRecs_top a s hsle,
        crtBox_flatten_length a _ _ _ B (fun x => by
          unfold crtPadC; split_ifs
          · rw [List.getD_eq_getElem?_getD]
            rcases h : l[∑ j, x j * prefixProd s j]? with _ | y
            · simpa using hz
            · simp only [Option.getD_some]
              exact hlB y (List.mem_of_getElem? h)
          · exact hz), crtW_revAx a d le_rfl]
    rw [e1, hR₂bU, List.length_replicate, e2]
    nlinarith

/-! ### The deletion scan -/

/-- The mixed-radix digits of `K` in the radices `s`: `K / prefixProd s j % s j`. -/
def crtUnrank (K : ℕ) (j : Fin d) : ℕ := K / prefixProd s j % s j

lemma crtProd_pos (hs : ∀ j, 0 < s j) (m : ℕ) : 0 < crtProd s m :=
  Finset.prod_pos fun j _ => hs j

lemma crtProd_dvd {m m' : ℕ} (h : m ≤ m') : crtProd s m ∣ crtProd s m' :=
  Finset.prod_dvd_prod_of_subset _ _ _ fun j hj => by simp at hj ⊢; omega

/-- The mixed-radix digits of the value of a valid index are its digits. -/
theorem crtK_digits (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j) :
    ∀ m ≤ d, ∀ F < 2 ^ crtPre a m, crtVal a s m F = true →
      crtK a s m F < crtProd s m ∧
        ∀ j : Fin d, j.val < m → crtK a s m F / prefixProd s j % s j = crtDig a j F
  | 0, _, F, _, _ => ⟨by simp, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | m + 1, hm, F, hF, hv => by
      have h : m < d := by omega
      have hsle : ∀ j, s j ≤ 2 ^ a j := fun j => (hs j).2.le
      set M := 2 ^ crtPre a m
      have hMpos : 0 < M := by positivity
      have hF' : F / M < 2 ^ a ⟨m, h⟩ := by
        rw [crtPre_succ a h, pow_add] at hF; exact Nat.div_lt_of_lt_mul hF
      have hdec : F = F / M * M + F % M := (Nat.div_add_mod' F M).symm
      have hr : F % M < M := Nat.mod_lt _ hMpos
      rw [hdec, crtVal_succ a s h hF' hr] at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨ih₁, ih₂⟩ := crtK_digits hs m (by omega) (F % M) hr hv.1
      have hPm : prefixProd s ⟨m, h⟩ = crtProd s m := (crtProd_eq_prefixProd s h).symm
      rw [hdec, crtK_succ a s h hF' hr]
      refine ⟨?_, fun j hj => ?_⟩
      · rw [crtProd_succ s h]
        nlinarith [hv.2]
      · have hPj : prefixProd s j = crtProd s j.val := (crtProd_eq_prefixProd s j.isLt).symm
        have hPjpos : 0 < crtProd s j.val := crtProd_pos s (fun i => (hs i).1) _
        by_cases hjm : j.val < m
        · obtain ⟨Q, hQ⟩ := crtProd_dvd s (show j.val + 1 ≤ m by omega)
          rw [crtProd_succ s j.isLt] at hQ
          rw [hPj, hQ, crtDig_low a j hjm _ _ hr, ← ih₂ j hjm, hPj]
          rw [show crtK a s m (F % M) + F / M * (crtProd s j.val * s ⟨j.val, j.isLt⟩ * Q) =
              crtK a s m (F % M) + crtProd s j.val * (s j * (F / M * Q)) by
            simp only [Fin.eta]; ring,
            Nat.add_mul_div_left _ _ hPjpos, Nat.add_mul_mod_self_left]
        · have hj' : j = ⟨m, h⟩ := Fin.ext (by simp; omega)
          subst hj'
          rw [hPm, crtDig_top a h hF' hr, Nat.add_mul_div_right _ _ (crtProd_pos s
            (fun i => (hs i).1) m), Nat.div_eq_of_lt ih₁, Nat.zero_add, Nat.mod_eq_of_lt hv.2]

/-- The deleted records after the first `F` indices: the content at the mixed-radix digits of
`K`, for `K` below the count of valid indices. -/
def crtDelRecs {α : Type*} (D : (Fin d → ℕ) → α) (F : ℕ) : List α :=
  (List.range (crtCnt a s d F)).map fun K => D (crtUnrank s K)

/-- The deletion scan: the records at the valid indices of `str` (a box along `crtRevAx d` of
records of `B` symbols) onto `acc` (reversed), the others dropped; then back onto `str`. -/
def crtDelP (L : CrtAL T) (str acc zr bU tA : Fin T) : Pr P T Q A U :=
  .seq (ucopy zr bU tA)
    (.seq (crtALFull L (crtCMv bU tA str acc) (crtDrop bU tA str))
      (.seq (uclear bU) (crtMv acc str)))

theorem crtDel_runs (L : CrtAL T) (hL : L.Ok) {str acc zr bU tA : Fin T}
    (hreg : [str, acc, zr, bU, tA].Nodup)
    (hp : ∀ k ∈ [str, acc, zr, bU, tA], ¬ L.Prot k)
    (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (D : (Fin d → ℕ) → List (Fin (A + 4))) (B : ℕ) (hD : ∀ x, (D x).length = B)
    (R₀ : Regs T A) (hstr : R₀ str = (crtBox a (crtRevAx d) D 0).flatten)
    (hzr : (R₀ zr).length = B) (hacc : R₀ acc = []) (hbU : R₀ bU = []) (htA : R₀ tA = [])
    (hnF : R₀ L.nF = []) (htN : R₀ L.tN = []) (hfc : R₀ L.fc = [])
    (hsg : R₀ L.sg = binSyms (crtPre a d) (crtSig a s d))
    (hmq : R₀ L.mq = binSyms (crtPre a d) (crtMask a d))
    (hc0 : R₀ L.c0 = []) (hc1 : R₀ L.c1 = []) (hc2 : R₀ L.c2 = []) (hit : R₀ L.it = []) :
    crtRuns body (crtDelP L str acc zr bU tA) R₀
      (Function.update R₀ str
        ((List.range (crtProd s d)).map fun K => D (crtUnrank s K)).flatten)
      (2 ^ crtPre a d * (10 * B + 10 * crtPre a d + 29) + 25 * crtPre a d + 6 * B + 29) := by
  have hreg' := hreg
  regs_ne hreg'
  have hsle : ∀ j, s j ≤ 2 ^ a j := fun j => (hs j).2.le
  set W := crtPre a d with hW
  set N := 2 ^ W with hN
  have pstr := hp str (by simp)
  have pacc := hp acc (by simp)
  have pbU := hp bU (by simp)
  have ptA := hp tA (by simp)
  have h₁ := crtUcopy_runs (body := body) ‹zr ≠ bU› ‹zr ≠ tA› ‹bU ≠ tA› R₀ htA
  set R₁ := Function.update R₀ bU (List.replicate (R₀ zr).length tick ++ R₀ bU) with hR₁
  have hR₁bU : R₁ bU = List.replicate B tick := by simp [hR₁, hzr, hbU]
  set box := crtBox a (crtRevAx d) D 0 with hbox
  have hboxlen : box.length = N := by simp [hbox, crtW_revAx a d le_rfl, hN, hW]
  have hboxB : ∀ x ∈ box, x.length = B := by
    intro x hx
    simp only [hbox, crtBox, List.mem_map] at hx
    obtain ⟨n, _, rfl⟩ := hx
    exact hD _
  let Ψ : ℕ → Regs T A := fun F => Function.update (Function.update R₁ str
    ((box.drop F).flatten)) acc ((crtDelRecs a s D F).flatten.reverse)
  have hΨstr : ∀ F, Ψ F str = (box.drop F).flatten := fun F => by
    simp [Ψ, Function.update_of_ne ‹str ≠ acc›]
  have hΨacc : ∀ F, Ψ F acc = (crtDelRecs a s D F).flatten.reverse := fun F => by simp [Ψ]
  have hΨoth : ∀ F G k, k ≠ str → k ≠ acc → Ψ F k = Ψ G k := fun F G k h1 h2 => by
    simp [Ψ, Function.update_of_ne h1, Function.update_of_ne h2]
  have hRoth : ∀ F (R : Regs T A), (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      ∀ k, k ≠ str → k ≠ acc → ¬ L.Prot k → R k = R₁ k := fun F R hR k h1 h2 h3 => by
    rw [hR k h3]; simp [Ψ, Function.update_of_ne h1, Function.update_of_ne h2]
  have hRbU : ∀ F (R : Regs T A), (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      R bU = List.replicate B tick := fun F R hR => by
    rw [hRoth F R hR bU ‹str ≠ bU›.symm ‹acc ≠ bU›.symm pbU, hR₁bU]
  have hRtA : ∀ F (R : Regs T A), (∀ k, ¬ L.Prot k → R k = Ψ F k) → R tA = [] :=
    fun F R hR => by
      rw [hRoth F R hR tA ‹str ≠ tA›.symm ‹acc ≠ tA›.symm ptA, hR₁,
        Function.update_of_ne ‹bU ≠ tA›.symm, htA]
  have hlenF : ∀ F < N, B ≤ ((box.drop F).flatten).length := by
    intro F hF
    rw [crt_length_drop_flatten box B hboxB, hboxlen]
    have : 1 ≤ N - F := by omega
    nlinarith
  have hV : ∀ F < N, crtVal a s d F = true → ∀ R : Regs T A,
      (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      crtRuns body (crtCMv bU tA str acc) R (fun k => if L.Prot k then R k else Ψ (F + 1) k)
        (4 * B + 4) := by
    intro F hF hv R hR
    have hc : F < box.length := by rw [hboxlen]; exact hF
    have hRstr : R str = (box.drop F).flatten := by rw [hR str pstr, hΨstr]
    have hRacc : R acc = (crtDelRecs a s D F).flatten.reverse := by rw [hR acc pacc, hΨacc]
    obtain ⟨htake, hdrop⟩ := crt_take_drop_flatten box B hboxB F hc
    have h := crtCMv_runs (body := body) (c := bU) (t := tA) (src := str) (dst := acc)
      (by regs_nodup) R (hRtA F R hR)
      (by rw [hRbU F R hR, hRstr, List.length_replicate]; exact hlenF F hF)
    refine crtRuns_mono (crtRuns_congr h ?_) (by rw [hRbU F R hR, List.length_replicate])
    have hcs : crtCnt a s d (F + 1) = crtCnt a s d F + 1 := by rw [crtCnt_succ_arg, hv]; rfl
    have hrec : box[F] = D (crtUnrank s (crtCnt a s d F)) := by
      rw [show box[F] = D (crtDec a (crtRevAx d) F 0) from crtBox_getElem a _ D 0 F hc,
        crtDec_revAx_full a (by omega), (crtCnt_main a s hsle d le_rfl).2 F hF hv]
      congr 1
      funext j
      exact ((crtK_digits a s hs d le_rfl F hF hv).2 j j.isLt).symm
    funext k
    by_cases k1 : k = acc
    · rw [k1]
      simp only [Function.update_self, pacc, ↓reduceIte, hΨacc, crtDelRecs, hcs,
        List.range_succ, List.map_append, List.flatten_append, List.reverse_append,
        hRbU F R hR, List.length_replicate, hRstr, htake, hRacc, hrec]
      simp [crtDelRecs]
    · rw [Function.update_of_ne k1]
      by_cases k2 : k = str
      · rw [k2]
        simp only [Function.update_self, pstr, ↓reduceIte, hΨstr, hRbU F R hR,
          List.length_replicate, hRstr, hdrop]
      · rw [Function.update_of_ne k2]
        by_cases hk : L.Prot k
        · simp [hk]
        · simp only [hk, ↓reduceIte]
          rw [hR k hk, hΨoth F (F + 1) k k2 k1]
  have hI : ∀ F < N, crtVal a s d F = false → ∀ R : Regs T A,
      (∀ k, ¬ L.Prot k → R k = Ψ F k) →
      crtRuns body (crtDrop bU tA str) R (fun k => if L.Prot k then R k else Ψ (F + 1) k)
        (4 * B + 4) := by
    intro F hF hv R hR
    have hc : F < box.length := by rw [hboxlen]; exact hF
    have hRstr : R str = (box.drop F).flatten := by rw [hR str pstr, hΨstr]
    obtain ⟨_, hdrop⟩ := crt_take_drop_flatten box B hboxB F hc
    have h := crtUsub_runs (body := body) (a := bU) (b := str) (t := tA) ‹str ≠ bU›.symm
      ‹bU ≠ tA› ‹str ≠ tA› R (hRtA F R hR)
    refine crtRuns_mono (crtRuns_congr h ?_) (by rw [hRbU F R hR, List.length_replicate])
    have hcs : crtCnt a s d (F + 1) = crtCnt a s d F := by rw [crtCnt_succ_arg, hv]; rfl
    funext k
    by_cases k2 : k = str
    · rw [k2]
      simp only [Function.update_self, pstr, ↓reduceIte, hΨstr, hRbU F R hR,
        List.length_replicate, hRstr, hdrop]
    · rw [Function.update_of_ne k2]
      by_cases hk : L.Prot k
      · simp [hk]
      · simp only [hk, ↓reduceIte]
        by_cases k1 : k = acc
        · rw [k1, hR acc pacc, hΨacc, hΨacc, crtDelRecs, crtDelRecs, hcs]
        · rw [hR k hk, hΨoth F (F + 1) k k2 k1]
  have h₂ := crtALFull_runs a s L hL le_rfl hs hV hI R₁
    (fun k hk => by
      by_cases k1 : k = acc
      · rw [k1]; simp [Ψ, hR₁, Function.update_of_ne ‹acc ≠ bU›, hacc, crtDelRecs, crtCnt]
      · by_cases k2 : k = str
        · rw [k2]; simp [Ψ, Function.update_of_ne ‹str ≠ acc›, hR₁,
            Function.update_of_ne ‹str ≠ bU›, hstr]
        · simp [Ψ, Function.update_of_ne k1, Function.update_of_ne k2])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).1.symm, hnF])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.1.symm, htN])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.1.symm, hfc])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.1.symm, hsg, hW])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.2.1.symm, hmq, hW])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.2.2.1.symm, hc0])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.2.2.2.1.symm, hc1])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.2.2.2.2.1.symm, hc2])
    (by simp [hR₁, (CrtAL.ne_of_not_prot pbU).2.2.2.2.2.2.2.2.symm, hit])
  set R₂ := fun k => if L.Prot k then R₁ k else Ψ N k with hR₂
  have h₃ := crtClear_runs (body := body) bU R₂
  have h₄ := crtMv_runs (body := body) ‹str ≠ acc›.symm (Function.update R₂ bU [])
  have hR₂str : R₂ str = [] := by
    simp [hR₂, pstr, hΨstr, ← hboxlen]
  have hR₂acc : R₂ acc = (crtDelRecs a s D N).flatten.reverse := by simp [hR₂, pacc, hΨacc]
  have hR₂bU : R₂ bU = List.replicate B tick := by
    simp [hR₂, pbU, Ψ, Function.update_of_ne ‹str ≠ bU›.symm,
      Function.update_of_ne ‹acc ≠ bU›.symm, hR₁bU]
  have hcN : crtCnt a s d N = crtProd s d := (crtCnt_main a s hsle d le_rfl).1
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ h₄)))
    ?_) ?_
  · funext k
    by_cases k1 : k = str
    · rw [k1]
      simp only [Function.update_self, Function.update_of_ne ‹str ≠ bU›, hR₂str, hR₂acc,
        Function.update_of_ne ‹acc ≠ bU›, Function.update_of_ne ‹str ≠ acc›, List.reverse_reverse,
        List.append_nil, crtDelRecs, hcN]
    · rw [Function.update_of_ne k1, Function.update_of_ne k1]
      by_cases k2 : k = acc
      · rw [k2]; simp [hacc]
      · rw [Function.update_of_ne k2]
        by_cases k3 : k = bU
        · rw [k3]; simp [hbU]
        · rw [Function.update_of_ne k3]
          by_cases hk : L.Prot k
          · simp [hR₂, hk, hR₁, Function.update_of_ne k3]
          · simp [hR₂, hk, Ψ, Function.update_of_ne k1, Function.update_of_ne k2, hR₁,
              Function.update_of_ne k3]
  · have e2 : ((Function.update R₂ bU []) acc).length ≤ N * B := by
      rw [Function.update_of_ne ‹acc ≠ bU›, hR₂acc, List.length_reverse, crtDelRecs, hcN]
      rw [List.length_flatten, List.map_map]
      have : ∀ x ∈ List.range (crtProd s d), ((List.length ∘ fun K => D (crtUnrank s K)) x) = B :=
        fun x _ => hD _
      rw [List.map_congr_left this, List.map_const', List.sum_replicate, List.length_range,
        smul_eq_mul]
      have h1 := hcN ▸ crtCnt_mono a s d (show N ≤ N from le_rfl)
      have h2 : crtCnt a s d N ≤ N := by
        unfold crtCnt; exact (List.length_filter_le _ _).trans (by simp)
      rw [hcN] at h2
      nlinarith
    rw [hzr, hR₂bU, List.length_replicate]
    nlinarith

end Pad

end IntegerMultBounds.MathlibTM2.Fast
