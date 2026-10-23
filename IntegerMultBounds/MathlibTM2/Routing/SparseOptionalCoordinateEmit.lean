module

public import IntegerMultBounds.MathlibTM2.Routing.SparseSourceCoordinateEmit
public import IntegerMultBounds.MathlibTM2.Routing.SparseAbsentCoordinateEmit
public import IntegerMultBounds.MathlibTM2.Host.WordTape

/-! A live activity bit selects present or absent source-coordinate emission.
The activity tape is read without consumption; no value is unrolled into code. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sparseOptionalCoordinateProgram (activity last pos wire one selector gap dst tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (.act (WordCmd.peekRp activity symBit))
    (.cond (·.flag) (sparseSourceCoordinateProgram last pos wire one selector gap dst tx ty tz cy)
      (sparseAbsentCoordinateProgram last pos wire selector gap dst tx ty tz cy))

theorem sparseOptionalCoordinate_exec (body : P → Pr P T Q A U)
    (last pos wire one selector gap dst tx ty tz cy : Fin T)
    (hregs : [last, pos, wire, one, selector, gap, dst, tx, ty, tz].Nodup)
    (hcyWire : cy ≠ wire) (hcyOne : cy ≠ one) (hcyLast : cy ≠ last) (hcyPos : cy ≠ pos)
    (activity : Fin T) (enabled : Bool) (rest : List (Fin (A + 4)))
    (L Ls N position q : ℕ) (hN : N < 2 ^ L) (hpos : position < N) (hq : q + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hlast : S.R last = binSyms L (N - 1)) (hposition : S.R pos = binSyms L position)
    (hwire : S.R wire = binSyms Ls q) (hone : S.R one = binSyms Ls 1)
    (hselector : S.R selector = []) (hgap : S.R gap = [])
    (hactivity : S.R activity = bitSymbol enabled :: rest)
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 16 * L + 16 * Ls + 37 ∧
      Exec body (sparseOptionalCoordinateProgram activity last pos wire one selector gap dst tx ty tz cy)
        (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (binSyms L (N - 1 - position) ++ separator :: (binSyms Ls (if enabled then q + 1 else 0) ++ separator :: S.R dst)) }) := by
  let v₁ := { v with flag := enabled }
  have hp : (WordCmd.peekRp activity symBit : Act T Q A U).run (mk v S) = mk v₁ S := by
    simp [WordCmd.peekRp, Action.run, hactivity, v₁]
  cases enabled with
  | true =>
    obtain ⟨v₂, hu₂, he₂⟩ := sparseSourceCoordinate_exec body last pos wire one selector gap dst tx ty tz cy
      hregs hcyWire hcyOne hcyLast hcyPos L Ls N position q hN hpos hq v₁ S hlast hposition hwire hone hselector hgap htx hty htz
    refine ⟨v₂, 1 + ((16 * L + 16 * Ls + 35) + 1), hu₂, by omega, ?_⟩
    exact Exec.seq (hp ▸ Exec.act (body := body) (WordCmd.peekRp activity symBit) (mk v S))
      (Exec.cond_true (by rfl) he₂)
  | false =>
    have hn := hregs
    regs_ne hn
    obtain ⟨v₂, hu₂, he₂⟩ := sparseAbsentCoordinate_exec body last pos wire selector gap dst tx ty tz cy
      (by regs_nodup) hcyLast hcyPos L Ls N position hN hpos v₁ S hlast hposition
      (by rw [hwire, length_binSyms]) hselector hgap htx hty htz
    refine ⟨v₂, 1 + ((16 * L + 12 * Ls + 31) + 1), hu₂, by omega, ?_⟩
    exact Exec.seq (hp ▸ Exec.act (body := body) (WordCmd.peekRp activity symBit) (mk v S))
      (Exec.cond_false (by rfl) he₂)

end IntegerMultBounds.MathlibTM2.Routing
