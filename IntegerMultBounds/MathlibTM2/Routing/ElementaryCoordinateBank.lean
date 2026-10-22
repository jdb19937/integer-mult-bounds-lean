module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryRowExponent
public import IntegerMultBounds.MathlibTM2.Routing.ElementarySourceCoordinate
public import IntegerMultBounds.MathlibTM2.Routing.UnaryPredecessor

/-! One fixed bank for compiling elementary instruction coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

inductive ElementaryCoordinateReg where
  | width | target | source
  | targetUnary | sourceUnary | gap | rowExp | renamed | coord | high
  | scratch (i : Fin 7)
  deriving DecidableEq

def elementaryCoordinateInitialBank {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCoordinateReg → Fin T) (target source : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R (rg .targetUnary) (List.replicate target tick))
    (rg .sourceUnary) (List.replicate source tick)) (rg .gap) (List.replicate (target - 1) tick)

def elementaryCoordinateInitialProgram {T Q A : ℕ} {P U : Type}
    (rg : ElementaryCoordinateReg → Fin T) : Pr P T Q A U :=
  .seq (toUnary (rg .target) (rg .targetUnary) (rg (.scratch 2)) (rg (.scratch 3)) (rg (.scratch 4)))
    (.seq (toUnary (rg .source) (rg .sourceUnary) (rg (.scratch 2)) (rg (.scratch 3)) (rg (.scratch 4)))
      (unaryPredecessorProgram (rg .targetUnary) (rg .gap) (rg (.scratch 3)) (rg (.scratch 4))))

def elementaryCoordinateFinalBank {T A n : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCoordinateReg → Fin T) (L : ℕ) (target source : Fin n) : Fin T → List (Fin (A + 4)) :=
  let q := ((elementarySwapSpec target).coordinate source).val
  Function.update (Function.update (Function.update (Function.update R
    (rg .rowExp) (List.replicate (n - (target.val + (elementarySwapSpec target).w)) tick))
    (rg .renamed) (binSyms L q)) (rg .coord) (List.replicate q tick))
    (rg .high) (List.replicate (n - (q + 1)) tick)

def elementaryCoordinateFinalProgram {T Q A : ℕ} {P U : Type}
    (rg : ElementaryCoordinateReg → Fin T) : Pr P T Q A U :=
  .seq (elementaryRowExponentProgram (rg .targetUnary) (rg .width) (rg .target)
    (rg (.scratch 0)) (rg (.scratch 1)) (rg .rowExp) (rg (.scratch 2))
    (rg (.scratch 3)) (rg (.scratch 4)) (rg (.scratch 5)) (rg (.scratch 6)))
    (.seq (configurationChooseProgram (rg .sourceUnary) (rg .source) (rg .target) (rg .renamed)
      (rg (.scratch 3)) (rg (.scratch 4)))
      (.seq (toUnary (rg .renamed) (rg .coord) (rg (.scratch 2)) (rg (.scratch 3)) (rg (.scratch 4)))
        (unaryComplementProgram (rg .width) (rg .renamed) (rg (.scratch 0)) (rg (.scratch 1))
          (rg .high) (rg (.scratch 2)) (rg (.scratch 3)) (rg (.scratch 4)) (rg (.scratch 5)) (rg (.scratch 6)))))

end IntegerMultBounds.MathlibTM2.Routing
