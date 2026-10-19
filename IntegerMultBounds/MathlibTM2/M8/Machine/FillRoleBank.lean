module

public import IntegerMultBounds.Machine.RecursiveXorRoleBank
public import IntegerMultBounds.Machine.RecursiveRoleSerialization

/-!
# Filling a role on the recursive role bank

`RecursiveXorRoleBank` runs one pointwise binary symbol operation from a source role into a
destination role, on the permanent role/scratch/six-header bank. The same placement runs any
pointwise operation (`program`, `realizes`). With a constant symbol it fills the destination role
(`fillProgram`, `fill_roles`): the zero bit zeroes a stream, and the blank symbol clears a tape.
The source role is any other role of the same volume and is only read.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.FillRoleBank
noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveShiftRoleBank (common)
open RecursiveXorRoleBank (controls commonPorts commonPorts_injective word updated)
variable {t u n : ℕ}

/-- One pointwise operation from the source role into the destination role. -/
def program (op : Fin (prime+4) → Fin (prime+4) → Fin (prime+4)) (g : PointwiseRoleGate.Gate t) :=
  Placement.placed (PointwiseBinaryNormalized.program op)
    (CleanSubbank.placement (id : Fin 4 → Fin 4) (commonPorts (u := u) g) (commonPorts_injective g))

private theorem common_payload (g : PointwiseRoleGate.Gate t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (bs : List Bool) (aux : Tapes u prime) (x y : Fin n → Fin (prime+4))
    (hhx : roles.head g.src = 0) (hhy : roles.head g.dst = 0)
    (htx : roles.tape g.src = word x) (hty : roles.tape g.dst = word y) :
    SharedBank.payload (common roles hs ((controls bs).append aux)) (commonPorts g) =
      PointwiseBinaryNormalized.bank
        (PointwiseBinaryNormalized.pair (fun _ => blank) (fun _ => blank) 0 0 x y) bs := by
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> simp [common,commonPorts,Tapes.append,Fin.addCases,hhx,hhy,
      PointwiseBinaryNormalized.pair,
      controls,CountedLoopReuseAlphabet.controls,StackPop.bank] <;> omega
  · funext i
    fin_cases i <;> simp [common,commonPorts,Tapes.append,Fin.addCases,htx,hty,word,
      PointwiseBinaryNormalized.pair,
      controls,CountedLoopReuseAlphabet.controls,StackPop.bank] <;> omega

private theorem common_frame (g : PointwiseRoleGate.Gate t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (bs : List Bool) (aux : Tapes u prime) (x : Fin n → Fin (prime+4)) :
    SharedBank.strip (common roles hs ((controls bs).append aux)) (commonPorts g) =
      SharedBank.strip (common (updated roles g x) hs ((controls bs).append aux)) (commonPorts g) := by
  have selected : ∃ j, commonPorts (u := u) g j = Fin.castAdd (7+(2+u)) g.dst := ⟨1,rfl⟩
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases with
    | left i =>
      by_cases hi : i = g.dst
      · subst i; simp [selected]
      · simp only [common,Tapes.append,Fin.addCases_left,updated,SharedPlacementAlphabet.setTape,
          Function.update_of_ne hi]
    | right i => simp only [common,Tapes.append,Fin.addCases_right]
  · funext i
    induction i using Fin.addCases with
    | left i =>
      by_cases hi : i = g.dst
      · subst i; simp [selected]
      · simp only [common,Tapes.append,Fin.addCases_left,updated,SharedPlacementAlphabet.setTape,
          Function.update_of_ne hi]
    | right i => simp only [common,Tapes.append,Fin.addCases_right]

/-- One pointwise operation on the original source/destination roles. Headers, clock,
stream-length descriptor, scratch, spectators and auxiliary tapes survive. -/
theorem realizes (op : Fin (prime+4) → Fin (prime+4) → Fin (prime+4)) (g : PointwiseRoleGate.Gate t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (bs : List Bool) (aux : Tapes u prime) (x y : Fin n → Fin (prime+4))
    (hhx : roles.head g.src = 0) (hhy : roles.head g.dst = 0)
    (htx : roles.tape g.src = word x) (hty : roles.tape g.dst = word y)
    (hn : Counter.value bs = n) :
    HoareTime (program (u := u) op g)
      (fun w => w = CleanSubbank.bank (common roles hs ((controls bs).append aux)))
      (fun w => w = CleanSubbank.bank
        (common (updated roles g (fun i => op (x i) (y i))) hs ((controls bs).append aux)))
      (14*n+14*bs.length+33) := by
  apply CleanSubbank.realizes _ id (commonPorts g) Function.injective_id (commonPorts_injective g)
    _ _ (PointwiseBinaryNormalized.bank (PointwiseBinaryNormalized.pair (fun _ => blank) (fun _ => blank) 0 0 x y) bs)
    (PointwiseBinaryNormalized.bank (PointwiseBinaryNormalized.pair (fun _ => blank) (fun _ => blank) 0 0 x
      (fun i => op (x i) (y i))) bs) _
  · exact (SharedBankFrames.payload_identity _).trans (common_payload g roles hs bs aux x y hhx hhy htx hty).symm
  · exact (SharedBankFrames.payload_identity _).trans (common_payload g _ hs bs aux x _
      (by simpa [updated,SharedPlacementAlphabet.setTape,Function.update_of_ne g.distinct] using hhx)
      (by simp [updated,SharedPlacementAlphabet.setTape])
      (by simpa [updated,SharedPlacementAlphabet.setTape,Function.update_of_ne g.distinct] using htx)
      (by simp [updated,SharedPlacementAlphabet.setTape])).symm
  · exact SharedBankFrames.strip_identity _
  · exact SharedBankFrames.strip_identity _
  · exact common_frame g roles hs bs aux _
  · exact PointwiseBinaryNormalized.array_hoare op _ _ 0 0 x y bs hn


/-- The constant symbol `s`. -/
def fillSymbol (s : Fin 4) (_ _ : Fin (prime+4)) : Fin (prime+4) := RecursiveRoleSerialization.encode s

/-- Fill the destination role with the symbol `s`. -/
def fillProgram (s : Fin 4) (g : PointwiseRoleGate.Gate t) := program (u := u) (fillSymbol s) g

/-- On role data, a fill writes `s` at every position of the destination role. -/
theorem fill_roles {v : RecursiveInterchangeLayout.Descriptor} (s : Fin 4)
    (data : Fin t → Fin (RecursiveInterchangeLayout.volume prime v) → Fin 4) (g : PointwiseRoleGate.Gate t) :
    updated (RecursiveRoleSerialization.roles data) g
      (fun i => fillSymbol s (RecursiveRoleSerialization.encode (data g.src i))
        (RecursiveRoleSerialization.encode (data g.dst i))) =
      RecursiveRoleSerialization.roles (Function.update data g.dst (fun _ => s)) := by
  simp only [fillSymbol, updated]
  rw [← RecursiveRoleSerialization.source_eq_word (fun _ => s)]
  exact RecursiveRoleSerialization.roles_update data g.dst _

end
end IntegerMultBounds.MathlibTM2.M8.Machine.FillRoleBank
