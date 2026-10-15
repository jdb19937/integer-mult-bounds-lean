module

public import IntegerMultBounds.MathlibTM2.Fast.CRTBase

/-!
# An address-visible runtime fiber loop

Unlike the protected-register premise of `crtALFull_runs`, this loop exposes
the exact binary address to its arbitrary host-program body. Its unary count
is supplied at runtime and restored. The index starts at binary zero; each
body preserves the index, then a fixed binary increment advances it.
The body may therefore copy the index into the descriptor evaluator's bank.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Binary increment changes only the index register; temporary storage is
restored. The carry parameter names a local scan slot, not a modified stack. -/
theorem crtControlIndexStep_runs {index tmp : Fin T} (hne : index ≠ tmp)
    (carry : Fin T) (W F : ℕ) (R : Regs T A)
    (hindex : R index = binSyms W F) (htmp : R tmp = []) :
    crtRuns body (countIter index tmp carry) R
      (Function.update R index (binSyms W (F + 1))) (4 * W + 5) := by
  apply crtRuns_of_exec
  intro v S hS
  obtain ⟨v', hu, he⟩ := countIter_exec body hne carry v S
    (hS ▸ hindex) (hS ▸ htmp)
  refine ⟨v', _, hu, le_rfl, ?_⟩
  simpa only [hS] using he

/-- The data registers at one loop boundary, with the known address and
empty increment scratch installed. -/
def crtControlIndexRegs (index tmp : Fin T) (W F : ℕ) (R : Regs T A) : Regs T A :=
  Function.update (Function.update R index (binSyms W F)) tmp []

/-- A fixed host program with a runtime unary count and binary address. -/
def crtControlIndexedLoop (count saved index tmp carry : Fin T)
    (p : Pr P T Q A U) : Pr P T Q A U :=
  crtFor count saved (.seq p (countIter index tmp carry))

/-- The body sees address `F` explicitly, while the unary count is private
to the loop. It returns the same address; the loop performs the increment.
All four control registers are preserved by the body. -/
def CrtControlIndexedBody (count saved index tmp : Fin T) (W N b : ℕ)
    (p : Pr P T Q A U) (Ψ : ℕ → Regs T A) : Prop :=
  ∀ F < N, ∀ R : Regs T A,
    R index = binSyms W F → R tmp = [] →
    (∀ k, k ≠ count → k ≠ saved → k ≠ index → k ≠ tmp → R k = Ψ F k) →
    crtRuns body p R
      (fun k => if k = count ∨ k = saved ∨ k = index ∨ k = tmp then R k else Ψ (F + 1) k) b

/-- Actual indexed iteration: unary count and its saved stack are restored,
the index ends at `N`, and increment scratch is empty. Binary representations
are width-limited; `N ≤ 2^W` suffices for distinct addresses throughout the loop. -/
theorem crtControlIndexedLoop_runs {count saved index tmp : Fin T}
    (hreg : [count, saved, index, tmp].Nodup) (carry : Fin T)
    {W N b : ℕ} {p : Pr P T Q A U} {Ψ : ℕ → Regs T A}
    (hp : CrtControlIndexedBody (body := body) count saved index tmp W N b p Ψ)
    (ticks : List (Fin (A + 4))) (hlen : ticks.length = N) :
    crtRuns body (crtControlIndexedLoop count saved index tmp carry p)
      (crtForRegs count saved (crtControlIndexRegs index tmp W 0 (Ψ 0)) ticks [])
      (crtForRegs count saved (crtControlIndexRegs index tmp W N (Ψ N)) ticks [])
      (N * (b + 4 * W + 10) + 4) := by
  have hreg' := hreg
  regs_ne hreg'
  have hi : crtIter (body := body) (.seq p (countIter index tmp carry)) count saved
      (fun F => crtControlIndexRegs index tmp W F (Ψ F)) (b + (4 * W + 5)) N := by
    intro F hF R hR
    have hindex : R index = binSyms W F := by
      rw [hR index (Ne.symm ‹count ≠ index›) (Ne.symm ‹saved ≠ index›)]
      simp [crtControlIndexRegs, ‹index ≠ tmp›]
    have htmp : R tmp = [] := by
      rw [hR tmp (Ne.symm ‹count ≠ tmp›) (Ne.symm ‹saved ≠ tmp›)]
      simp [crtControlIndexRegs]
    have hdata : ∀ k, k ≠ count → k ≠ saved → k ≠ index → k ≠ tmp → R k = Ψ F k := by
      intro k hc hs hi ht
      rw [hR k hc hs]
      simp [crtControlIndexRegs, hi, ht]
    have hbody := hp F hF R hindex htmp hdata
    let R₁ : Regs T A := fun k =>
      if k = count ∨ k = saved ∨ k = index ∨ k = tmp then R k else Ψ (F + 1) k
    have hstep := crtControlIndexStep_runs (body := body) ‹index ≠ tmp› carry W F R₁
      (by simp [R₁, hindex]) (by simp [R₁, htmp])
    refine crtRuns_congr (crtRuns_seq hbody hstep) ?_
    funext k
    by_cases hc : k = count
    · subst k
      simp [R₁, Function.update_of_ne ‹count ≠ index›]
    · by_cases hs : k = saved
      · subst k
        simp [R₁, Function.update_of_ne ‹saved ≠ index›]
      · by_cases hi : k = index
        · subst k
          simp [hc, hs, crtControlIndexRegs, ‹index ≠ tmp›]
        · by_cases ht : k = tmp
          · subst k
            simp [hc, hs, hi, R₁, crtControlIndexRegs, htmp]
          · simp [hc, hs, hi, ht, R₁, crtControlIndexRegs]
  exact crtRuns_mono (crtFor_runs ‹count ≠ saved› hi ticks hlen) (by ring_nf; exact le_rfl)

/-- Initialize a binary address and construct the unary fiber count from
runtime exponent width, iterate, then clear the address and count. -/
def crtControlIndexedFull (width exponent count saved index tmp spare carry : Fin T)
    (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (zeroBits width index tmp)
    (.seq (crtPush count tick)
      (.seq (upow2 exponent count tmp spare)
        (.seq (crtControlIndexedLoop count saved index tmp carry p)
          (.seq (uclear index) (uclear count)))))

/-- Complete runtime setup and cleanup for a power-of-two fiber loop.
`Ψ` describes the data evolution, with the loop workspace empty at boundaries;
the width registers and second power-construction scratch are preserved by
that evolution. The fixed body receives the exact binary address as before. -/
theorem crtControlIndexedFull_runs {width exponent count saved index tmp spare : Fin T}
    (hreg : [width, exponent, count, saved, index, tmp, spare].Nodup) (carry : Fin T)
    {W L b : ℕ} {p : Pr P T Q A U} {Ψ : ℕ → Regs T A}
    (hwidth : (Ψ 0 width).length = W) (hexponent : (Ψ 0 exponent).length = L)
    (hclean : ∀ F, Ψ F count = [] ∧ Ψ F saved = [] ∧ Ψ F index = [] ∧
      Ψ F tmp = [] ∧ Ψ F spare = [])
    (_hfixed : ∀ F, Ψ F width = Ψ 0 width ∧ Ψ F exponent = Ψ 0 exponent)
    (hp : CrtControlIndexedBody (body := body) count saved index tmp W (2 ^ L) b p Ψ) :
    crtRuns body (crtControlIndexedFull width exponent count saved index tmp spare carry p)
      (Ψ 0) (Ψ (2 ^ L))
      (2 ^ L * (b + 4 * W + 16) + 6 * W + 9 * L + 17) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨hc, hs, hi, ht, hu⟩ := hclean 0
  have h₁ := crtZeroBits_runs (body := body) ‹width ≠ index› ‹width ≠ tmp› ‹index ≠ tmp›
    (Ψ 0) ht
  simp only [hwidth, hi, List.append_nil] at h₁
  let R₁ := Function.update (Ψ 0) index (binSyms W 0)
  have h₂ := crtPush_runs (body := body) count tick R₁
  let R₂ := Function.update R₁ count (tick :: R₁ count)
  have h₂count : R₂ count = [tick] := by simp [R₂, R₁, ‹count ≠ index›, hc]
  have h₂exp : (R₂ exponent).length = L := by
    simp [R₂, R₁, ‹exponent ≠ count›, ‹exponent ≠ index›, hexponent]
  have h₃ := crtUpow2_runs (body := body)
    (a := exponent) (b := count) (t₁ := tmp) (t₂ := spare) (by regs_nodup) R₂
    (by simp [R₂, R₁, Ne.symm, *]) (by simp [R₂, R₁, Ne.symm, *])
  rw [h₂count, h₂exp] at h₃
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons,
    List.length_nil] at h₃
  let B := fun F => crtForRegs count saved (crtControlIndexRegs index tmp W F (Ψ F))
    (List.replicate (2 ^ L) tick) []
  have hsetup : Function.update R₂ count (List.replicate (2 ^ L) tick) = B 0 := by
    funext k
    by_cases hkc : k = count
    · subst k; simp [B, crtForRegs]
    · by_cases hks : k = saved
      · subst k; simp [B, crtForRegs, R₂, R₁, *]
      · by_cases hki : k = index
        · subst k; simp [B, crtForRegs, crtControlIndexRegs, R₂, R₁, *]
        · by_cases hkt : k = tmp
          · subst k; simp [B, crtForRegs, crtControlIndexRegs, R₂, R₁, hkc, hks, hki, ht]
          · simp [B, crtForRegs, crtControlIndexRegs, R₂, R₁, hkc, hks, hki, hkt]
  have hloop := crtControlIndexedLoop_runs (body := body)
    (count := count) (saved := saved) (index := index) (tmp := tmp) (by regs_nodup)
    carry hp (List.replicate (2 ^ L) tick) (by simp)
  change crtRuns body _ (B 0) (B (2 ^ L)) _ at hloop
  have h₄ := crtClear_runs (body := body) index (B (2 ^ L))
  have hindexlen : (B (2 ^ L) index).length = W := by
    simp [B, crtForRegs, crtControlIndexRegs, Ne.symm, *]
  rw [hindexlen] at h₄
  have h₅ := crtClear_runs (body := body) count (Function.update (B (2 ^ L)) index [])
  have hcountlen : (Function.update (B (2 ^ L)) index [] count).length = 2 ^ L := by
    simp [B, crtForRegs, ‹count ≠ index›]
  rw [hcountlen] at h₅
  have hfinal : Function.update (Function.update (B (2 ^ L)) index []) count [] = Ψ (2 ^ L) := by
    obtain ⟨hc', hs', hi', ht', _⟩ := hclean (2 ^ L)
    funext k
    by_cases hkc : k = count
    · subst k; simp [hc']
    · by_cases hks : k = saved
      · subst k; simp [B, crtForRegs, *]
      · by_cases hki : k = index
        · subst k; simp [hkc, hi']
        · by_cases hkt : k = tmp
          · subst k; simp [B, crtForRegs, crtControlIndexRegs, hkc, hks, hki, ht']
          · simp [B, crtForRegs, crtControlIndexRegs, hkc, hks, hki, hkt]
  have hrun := crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq
    (crtRuns_congr h₃ hsetup) (crtRuns_seq hloop (crtRuns_congr (crtRuns_seq h₄ h₅) hfinal))))
  exact crtRuns_mono hrun (by ring_nf; exact le_rfl)

end IntegerMultBounds.MathlibTM2.Fast
