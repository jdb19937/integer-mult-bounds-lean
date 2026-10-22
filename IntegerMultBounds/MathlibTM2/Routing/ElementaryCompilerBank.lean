module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCoordinates
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryHeaderExec
public import IntegerMultBounds.MathlibTM2.Routing.ElementarySourceMask
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryInstructionWrite

/-!
# One fixed bank for elementary instruction compilation

The coordinate and arithmetic stages share their seven scratch tapes. Only five
binary inputs and the output stream persist across calls; generated coordinates,
headers and mask are private intermediates to be cleared after serialization.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive ElementaryCompilerReg where
  | coordinate (r : ElementaryCoordinateReg)
  | rows | block | header (i : Fin 5) | mask | output
  deriving DecidableEq

def elementaryCompilerHeader (r : ElementaryHeaderReg) : ElementaryCompilerReg :=
  match r with
  | .rowExp => .coordinate .rowExp
  | .gapExp => .coordinate .gap
  | .target => .coordinate .targetUnary
  | .rows => .rows
  | .block => .block
  | .header i => .header i
  | .scratch i => .coordinate (.scratch i)

theorem elementaryCompilerHeader_injective : Function.Injective elementaryCompilerHeader := by
  intro r s h
  cases r <;> cases s <;> simp_all [elementaryCompilerHeader]

def elementaryCompilerWord (key : Fin 6) : ElementaryCompilerReg :=
  if h : key.val < 5 then .header ⟨key.val, h⟩ else .mask

def elementaryCompilerInputs : List ElementaryCompilerReg :=
  [.coordinate .width, .coordinate .target, .coordinate .source, .rows, .block, .output]

def elementaryCompilerPrivate : List ElementaryCompilerReg :=
  [.coordinate .targetUnary, .coordinate .sourceUnary, .coordinate .gap,
    .coordinate .rowExp, .coordinate .renamed, .coordinate .coord, .coordinate .high,
    .header 0, .header 1, .header 2, .header 3, .header 4, .mask]

def elementaryCompilerPrepare {T Q A : ℕ} {P U : Type}
    (rg : ElementaryCompilerReg → Fin T) : Pr P T Q A U :=
  .seq (.seq (elementaryCoordinateProgram (fun r => rg (.coordinate r)))
    (elementaryHeaderProgram (fun r => rg (elementaryCompilerHeader r))))
    (sourceMaskProgram (rg (.coordinate .coord)) (rg (.coordinate .high)) (rg .mask)
      (rg (.coordinate (.scratch 3))) (rg (.coordinate (.scratch 4))))

def elementaryCompilerProgram {T Q A : ℕ} {P U : Type}
    (rg : ElementaryCompilerReg → Fin T) : Pr P T Q A U :=
  .seq (elementaryCompilerPrepare rg)
    (.seq (elementaryInstructionWrite (fun key => rg (elementaryCompilerWord key)) (rg .output)
      (rg (.coordinate (.scratch 3))) (rg (.coordinate (.scratch 4))))
      (metadataClean (elementaryCompilerPrivate.map rg)))

/-- The compiled coordinate bank embedded in the full compiler register file. -/
def elementaryCompilerCoordinates {T A n : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (L : ℕ) (target source : Fin n) :=
  elementaryCoordinateFinalBank
    (elementaryCoordinateInitialBank R (fun r => rg (.coordinate r)) target.val source.val)
    (fun r => rg (.coordinate r)) L target source

def elementaryCompilerWords {n : ℕ} (rowBits triple : List Bool) (target : Fin n) : Fin 5 → List Bool :=
  elementaryHeaderWords rowBits (n - (target.val + (elementarySwapSpec target).w))
    (target.val - 1) triple (decide (target.val ≠ 0))

def elementaryCompilerHeaders {T A n : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (L : ℕ) (target source : Fin n) (rowBits triple : List Bool) :=
  elementaryHeaderBank (elementaryCompilerCoordinates R rg L target source)
    (fun r => rg (elementaryCompilerHeader r)) (elementaryCompilerWords rowBits triple target)

def elementaryCompilerReady {T A n : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (L : ℕ) (target source : Fin n) (rowBits triple : List Bool) :=
  Function.update (elementaryCompilerHeaders R rg L target source rowBits triple) (rg .mask)
    (binSyms n (2 ^ ((elementarySwapSpec target).coordinate source).val))

end IntegerMultBounds.MathlibTM2.Routing
