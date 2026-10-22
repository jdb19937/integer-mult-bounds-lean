module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob
public import IntegerMultBounds.GrowingCounterData

/-!
# Canonical zero-or-one header from tape nonemptiness

A unary coordinate tape is empty exactly at coordinate zero. The fixed program
reads that condition and writes the canonical interchange width, preserving its
input and every other tape.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binaryNonemptyBits (live : Bool) : List Bool := if live then [true] else []

theorem binaryNonemptyBits_canonical (live : Bool) :
    GrowingCounterData.Canonical (binaryNonemptyBits live) := by
  cases live
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem binaryNonemptyBits_value (live : Bool) :
    Counter.value (binaryNonemptyBits live) = live.toNat := by
  cases live <;> rfl

def binaryNonemptyProgram (src dst : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src)) (.cond (·.flag)
    (.act (.push (.rt dst) (fun _ => bitSymbol true) .done)) (.act .done))

/-- Read a live unary coordinate and generate its zero-or-one width header. -/
theorem binaryNonempty_exec (body : P → Pr P T Q A U) (src dst : Fin T)
    (v : HS T Q A U) (S : Stacks T A) (hdst : S.R dst = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binaryNonemptyProgram src dst) (mk v S) 3
        (mk v' { S with R := Function.update S.R dst ((binaryNonemptyBits (S.R src).head?.isSome).map bitSymbol) }) := by
  let v₁ := { v with flag := (S.R src).head?.isSome }
  have hp : (peekR src : Act T Q A U).run (mk v S) = mk v₁ S := rfl
  cases hs : (S.R src).head?.isSome with
  | false =>
    refine ⟨v₁, rfl, ?_⟩
    have he : Function.update S.R dst ((binaryNonemptyBits false).map bitSymbol) = S.R := by
      simp [binaryNonemptyBits, ← hdst]
    rw [he]
    exact Exec.seq (hp ▸ Exec.act (body := body) (peekR src) (mk v S))
      (Exec.cond_false (f := (·.flag)) (by exact hs) (Exec.act (body := body) .done (mk v₁ S)))
  | true =>
    have hr : (Action.push (.rt dst) (fun _ => bitSymbol true) .done : Act T Q A U).run (mk v₁ S) =
        mk v₁ { S with R := Function.update S.R dst ((binaryNonemptyBits true).map bitSymbol) } := by
      simp [Action.run, update_rt, hdst, binaryNonemptyBits]
    refine ⟨v₁, rfl, ?_⟩
    exact Exec.seq (hp ▸ Exec.act (body := body) (peekR src) (mk v S))
      (Exec.cond_true (f := (·.flag)) (by exact hs)
        (hr ▸ Exec.act (body := body) _ (mk v₁ S)))

end IntegerMultBounds.MathlibTM2.Routing
