module

public import IntegerMultBounds.Schoenhage.Ops

/-!
# Word programs on host stacks

The vendored Schönhage–Strassen multiplier is written as a word program (`Schoenhage.Cmd`) over a
bank of word tapes, with big-step semantics `Schoenhage.Exec`. Every primitive carries a host
implementation (`Prim.prog`, `Prim.hspec`: `HostSpec 3 nQ`, `Host/WordTape`), so a word program
runs directly on host stacks, without a multitape machine in between.

**Compilation** (`tcompile`): primitives by their host programs on the placed registers,
sequencing by sequencing, and the loop and branch tests by a peek at the tested register (`peekW`).
`cmdStates c` is the largest control-state count a primitive of `c` needs. `tcompile_exec`: for
`cmdStates c ≤ Q`, an execution of `c` within `k` steps gives a host execution of `tcompile ι c`
between the placed banks (`place`) within `3 (k + 1)` steps, every other stack and the `user`
component unchanged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host.WordCmd

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.Schoenhage (WTape Prim Cmd cells clen upd upd_slot upd_other StartsOne)

section Lemmas

variable {T A t : ℕ}

theorem cells_head_one (R : List (List Bool)) :
    (cells (a := A) R).head? = some (bitSymbol true) ↔ StartsOne ⟨[], R⟩ := by
  unfold StartsOne
  rcases R with _ | ⟨_ | ⟨b, w⟩, R⟩
  · simp [cells]
  · rw [cells_cons']; simp [separator, bitSymbol]
  · rw [cells_cons']; cases b <;> simp [bitSymbol]

variable {ι : Fin t → Fin T}

/-- Placing a primitive's tapes over a placed bank places the updated bank. -/
theorem place_place (hι : Function.Injective ι) {s : ℕ} {slot : Fin s → Fin t}
    (hs : Function.Injective slot) (S : Stacks T A) (σ : Fin t → WTape) (τ : Fin s → WTape) :
    place (place S ι σ) (ι ∘ slot) τ = place S ι (upd σ slot τ) := by
  have hj : Function.Injective (ι ∘ slot) := hι.comp hs
  ext1
  · rfl
  · rfl
  all_goals
    funext r
    by_cases hr : ∃ x, ι x = r
    · obtain ⟨x, rfl⟩ := hr
      by_cases hx : ∃ i, slot i = x
      · obtain ⟨i, rfl⟩ := hx
        first
          | rw [show ι (slot i) = (ι ∘ slot) i from rfl, place_L_at hj, Function.comp_apply,
              place_L_at hι, upd_slot σ hs]
          | rw [show ι (slot i) = (ι ∘ slot) i from rfl, place_R_at hj, Function.comp_apply,
              place_R_at hι, upd_slot σ hs]
      · have hoff : ∀ i, (ι ∘ slot) i ≠ ι x := fun i h => hx ⟨i, hι h⟩
        have hno : ∀ i, slot i ≠ x := fun i h => hx ⟨i, h⟩
        first
          | rw [place_L_off _ _ hoff, place_L_at hι, place_L_at hι, upd_other σ slot τ x hno]
          | rw [place_R_off _ _ hoff, place_R_at hι, place_R_at hι, upd_other σ slot τ x hno]
    · have hoff : ∀ x, ι x ≠ r := fun x h => hr ⟨x, h⟩
      have hoff' : ∀ i, (ι ∘ slot) i ≠ r := fun i => hoff (slot i)
      first
        | rw [place_L_off _ _ hoff', place_L_off _ _ hoff, place_L_off _ _ hoff]
        | rw [place_R_off _ _ hoff', place_R_off _ _ hoff, place_R_off _ _ hoff]

theorem upd_comp_self {s : ℕ} {slot : Fin s → Fin t} (hs : Function.Injective slot)
    (σ : Fin t → WTape) : upd σ slot (σ ∘ slot) = σ := by
  funext x
  by_cases hx : ∃ i, slot i = x
  · obtain ⟨i, rfl⟩ := hx; rw [upd_slot σ hs]; rfl
  · exact upd_other σ slot _ x fun i h => hx ⟨i, h⟩

/-- Placing the bank the registers already hold changes nothing. -/
theorem place_self (hι : Function.Injective ι) {S : Stacks T A} {σ : Fin t → WTape}
    (hL : ∀ x, S.L (ι x) = lcells (σ x).left) (hR : ∀ x, S.R (ι x) = cells (σ x).right) :
    place S ι σ = S := by
  ext1
  · rfl
  · rfl
  all_goals
    funext r
    by_cases h : ∃ x, ι x = r
    · obtain ⟨x, rfl⟩ := h
      first | rw [place_L_at hι, hL] | rw [place_R_at hι, hR]
    · first | exact place_L_off _ _ fun x hx => h ⟨x, hx⟩ | exact place_R_off _ _ fun x hx => h ⟨x, hx⟩

end Lemmas

/-! ### Compilation -/

section Compile

variable {a t T Q A : ℕ} {U P : Type}

/-- The control states the primitives of a word program need. -/
def cmdStates : Cmd a t → ℕ
  | .prim M _ _ => M.nQ
  | .seq c d => max (cmdStates c) (cmdStates d)
  | .loop _ b => cmdStates b
  | .cond _ c d => max (cmdStates c) (cmdStates d)

/-- Record in `flag` whether the right stack of register `r` is nonempty and in `sym` its top. -/
def peekW (r : Fin T) : Act T Q A U :=
  .peek (.rt r) (fun v o => { v with flag := o.isSome, sym := o }) .done

/-- The host program of a word program on the registers `ι`. -/
def tcompile (ι : Fin t → Fin T) : Cmd a t → Pr P T Q A U
  | .prim M slot _ => M.prog (ι ∘ slot)
  | .seq c d => .seq (tcompile ι c) (tcompile ι d)
  | .loop i b =>
      .seq (.act (peekW (ι i))) (.loop (·.flag) (.seq (tcompile ι b) (.act (peekW (ι i)))))
  | .cond i c d =>
      .seq (.act (peekW (ι i)))
        (.cond (fun v => decide (v.sym = some (bitSymbol true))) (tcompile ι c) (tcompile ι d))

theorem tcompile_noCalls (ι : Fin t → Fin T) :
    ∀ c : Cmd a t, NoCalls (tcompile (P := P) (Q := Q) (A := A) (U := U) ι c)
  | .prim M _ _ => M.hcalls _
  | .seq c d => ⟨tcompile_noCalls ι c, tcompile_noCalls ι d⟩
  | .loop _ b => ⟨trivial, tcompile_noCalls ι b, trivial⟩
  | .cond _ c d => ⟨trivial, tcompile_noCalls ι c, tcompile_noCalls ι d⟩

variable (body : P → Pr P T Q A U)

theorem peekW_run (r : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (peekW r : Act T Q A U).run (mk v S) =
      mk { v with flag := (S.R r).head?.isSome, sym := (S.R r).head? } S := rfl

/-- **Compilation is correct.** -/
theorem tcompile_exec {ι : Fin t → Fin T} (hι : Function.Injective ι) {c : Cmd a t}
    {σ σ' : Fin t → WTape} {k : ℕ} (h : Schoenhage.Exec c σ σ' k) (hQ : cmdStates c ≤ Q)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 3 * (k + 1) ∧
      Exec body (tcompile ι c) (mk v (place S ι σ)) m (mk v' (place S ι σ')) := by
  induction h generalizing v with
  | @prim M slot hinj σ hpre =>
    obtain ⟨v', m, hu, hm, he⟩ :=
      M.hspec body (ι ∘ slot) (hι.comp hinj) hQ (σ ∘ slot) hpre v (place S ι σ)
    rw [place_place hι hinj, place_place hι hinj, upd_comp_self hinj] at he
    exact ⟨v', m, hu, hm, he⟩
  | @seq c d σ σ₁ σ₂ k₁ k₂ h₁ h₂ ih₁ ih₂ =>
    simp only [cmdStates, max_le_iff] at hQ
    obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := ih₁ hQ.1 v
    obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := ih₂ hQ.2 v₁
    refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩
  | @loop_done i b σ hdone =>
    have hf : (place S ι σ).R (ι i) = [] := by rw [place_R_at hι, hdone]; rfl
    refine ⟨{ v with flag := ((place S ι σ).R (ι i)).head?.isSome, sym := ((place S ι σ).R (ι i)).head? },
      2, rfl, by omega, ?_⟩
    simp only [tcompile]
    exact Exec.seq (Exec.act (peekW (ι i)) _) (Exec.loop_false (by simp [peekW_run, hf]))
  | @loop_step i b σ σ₁ σ₂ k₁ k₂ hne h₁ h₂ ih₁ ih₂ =>
    have hb : cmdStates b ≤ Q := hQ
    have hf : ((place S ι σ).R (ι i)).head?.isSome = true := by
      rw [place_R_at hι, cells_head_isSome]; simpa using hne
    obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := ih₁ hb
      { v with flag := ((place S ι σ).R (ι i)).head?.isSome, sym := ((place S ι σ).R (ι i)).head? }
    obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := ih₂ hQ v₁
    simp only [tcompile] at he₂
    cases he₂ with
    | @seq _ _ _ _ _ m n hp hl =>
      cases hp
      refine ⟨v₂, 1 + (n₁ + 1 + n + 1), hu₂.trans hu₁, by omega, ?_⟩
      simp only [tcompile]
      exact Exec.seq (Exec.act (peekW (ι i)) _)
        (Exec.loop_true (by simpa [peekW_run] using hf)
          (Exec.seq he₁ (Exec.act (peekW (ι i)) _)) hl)
  | @cond_true i c d σ σ' k hone h₁ ih =>
    simp only [cmdStates, max_le_iff] at hQ
    obtain ⟨v₁, n, hu, hn, he⟩ := ih hQ.1
      { v with flag := ((place S ι σ).R (ι i)).head?.isSome, sym := ((place S ι σ).R (ι i)).head? }
    have ht : ((place S ι σ).R (ι i)).head? = some (bitSymbol true) := by
      rw [place_R_at hι, cells_head_one]; exact hone
    refine ⟨v₁, 1 + (n + 1), hu, by omega, ?_⟩
    simp only [tcompile]
    exact Exec.seq (Exec.act (peekW (ι i)) _) (Exec.cond_true (by simp [peekW_run, ht]) he)
  | @cond_false i c d σ σ' k hone h₁ ih =>
    simp only [cmdStates, max_le_iff] at hQ
    obtain ⟨v₁, n, hu, hn, he⟩ := ih hQ.2
      { v with flag := ((place S ι σ).R (ι i)).head?.isSome, sym := ((place S ι σ).R (ι i)).head? }
    have ht : ((place S ι σ).R (ι i)).head? ≠ some (bitSymbol true) := by
      rw [place_R_at hι, Ne, cells_head_one]; exact hone
    refine ⟨v₁, 1 + (n + 1), hu, by omega, ?_⟩
    simp only [tcompile]
    exact Exec.seq (Exec.act (peekW (ι i)) _) (Exec.cond_false (by simp [peekW_run, ht]) he)

/-- `tcompile_exec` for a run into a postcondition. -/
theorem tcompile_runs {ι : Fin t → Fin T} (hι : Function.Injective ι) {c : Cmd a t}
    {σ : Fin t → WTape} {Post : (Fin t → WTape) → Prop} {B : ℕ} (h : Schoenhage.Runs c σ Post B)
    (hQ : cmdStates c ≤ Q) (v : HS T Q A U) (S : Stacks T A) :
    ∃ σ', Post σ' ∧ ∃ v' m, v'.user = v.user ∧ m ≤ 3 * (B + 1) ∧
      Exec body (tcompile ι c) (mk v (place S ι σ)) m (mk v' (place S ι σ')) := by
  obtain ⟨σ', k, he, hq, hk⟩ := h
  obtain ⟨v', n, hu, hn, he'⟩ := tcompile_exec body hι he hQ v S
  exact ⟨σ', hq, v', n, hu, hn.trans (Nat.mul_le_mul_left _ (by omega)), he'⟩

end Compile

end IntegerMultBounds.MathlibTM2.Host.WordCmd
