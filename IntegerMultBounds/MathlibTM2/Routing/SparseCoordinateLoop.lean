module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateCall

/-! One fixed loop computes compact gaps from an ordered stream of absolute
coordinates. The trace bank records the executed archive, cursor and output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sparseCoordinateFrames (L Ls : ℕ) : List (ℕ × ℕ) → List (Fin (A + 4))
  | [] => []
  | (x, q) :: rest => binSyms L x ++ separator :: (binSyms Ls q ++ separator :: sparseCoordinateFrames L Ls rest)

def SparseCoordinatesReady (L : ℕ) (cursor : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | (x, _) :: rest => x + 1 < 2 ^ L ∧ cursor ≤ x ∧ SparseCoordinatesReady L (x + 1) rest

def sparseCoordinateTraceBank (R : Fin T → List (Fin (A + 4))) (rg : SparseCoordinateReg → Fin T)
    (L Ls cursor : ℕ) : List (ℕ × ℕ) → Fin T → List (Fin (A + 4))
  | [] => R
  | (x, q) :: rest => sparseCoordinateTraceBank
      (sparseCoordinateCallBank R rg L Ls x cursor q (sparseCoordinateFrames L Ls rest)) rg L Ls (x + 1) rest

def sparseCoordinateLoopBody (rg : SparseCoordinateReg → Fin T) : Pr P T Q A U :=
  .seq (sparseCoordinateCallProgram rg) (.act (peekR (rg .src)))

theorem sparseCoordinateLoop_exec (body : P → Pr P T Q A U)
    (rg : SparseCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (L Ls cursor : ℕ) (entries : List (ℕ × ℕ)) (hready : SparseCoordinatesReady L cursor entries)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = sparseCoordinateFrames L Ls entries)
    (hcursor : S.R (rg .cursor) = binSyms L cursor) (hone : S.R (rg .one) = binSyms L 1)
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .cursor → r ≠ .one → r ≠ .dst → S.R (rg r) = [])
    (hflag : v.flag = (sparseCoordinateFrames (A := A) L Ls entries).head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps = entries.length * (32 * L + 12 * Ls + 54) + 1 ∧
      Exec body (.loop (·.flag) (sparseCoordinateLoopBody rg)) (mk v S) steps
        (mk v' { S with R := sparseCoordinateTraceBank S.R rg L Ls cursor entries }) := by
  induction entries generalizing cursor v S with
  | nil =>
    refine ⟨v, 1, rfl, by simp, ?_⟩
    exact Exec.loop_false (by simpa only [sparseCoordinateFrames, List.head?_nil, Option.isSome_none, mk_var] using hflag)
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    obtain ⟨hx, hyx, hr⟩ := hready
    obtain ⟨v₁, hu₁, he₁⟩ := sparseCoordinateCall_exec body rg hrg L Ls x cursor q hx hyx
      (sparseCoordinateFrames L Ls rest) v S hsrc hcursor hone hblank
    let S₁ : Stacks T A := { S with R := sparseCoordinateCallBank S.R rg L Ls x cursor q (sparseCoordinateFrames L Ls rest) }
    have hi : S₁.R (rg .src) = sparseCoordinateFrames L Ls rest := by simp [S₁, sparseCoordinateCallBank, hrg.eq_iff]
    have hc : S₁.R (rg .cursor) = binSyms L (x + 1) := by simp [S₁, sparseCoordinateCallBank]
    have ho : S₁.R (rg .one) = binSyms L 1 := by simp [S₁, sparseCoordinateCallBank, hrg.eq_iff, hone]
    have hb : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .cursor → r ≠ .one → r ≠ .dst → S₁.R (rg r) = [] := by
      intro r hs ha hc ho hd
      simpa [S₁, sparseCoordinateCallBank, hrg.eq_iff, hs, ha, hc, hd] using hblank r hs ha hc ho hd
    let v₂ := { v₁ with flag := (sparseCoordinateFrames (A := A) L Ls rest).head?.isSome }
    have hp : (peekR (rg .src) : Act T Q A U).run (mk v₁ S₁) = mk v₂ S₁ := by
      simp only [peekR_run, hi]; rfl
    obtain ⟨v₃, n₃, hu₃, ht₃, he₃⟩ := ih (x + 1) hr v₂ S₁ hi hc ho hb rfl
    have hf : v.flag = true := by
      have hn : sparseCoordinateFrames (A := A) L Ls ((x, q) :: rest) ≠ [] := by
        intro he
        have hh := congrArg List.length he
        simp [sparseCoordinateFrames] at hh
      obtain ⟨a, as, he⟩ := List.exists_cons_of_ne_nil hn
      simpa only [he, List.head?_cons, Option.isSome_some] using hflag
    have hex := Exec.loop_true (body := body) (f := (·.flag)) (by simpa only [mk_var] using hf)
      (Exec.seq he₁ (hp ▸ Exec.act (body := body) (peekR (rg .src)) (mk v₁ S₁))) he₃
    refine ⟨v₃, (32 * L + 12 * Ls + 52) + n₃ + 2, hu₃.trans hu₁, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · exact Exec.cast hex (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
