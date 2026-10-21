module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.MetaPrepare
public import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! The stage-2 metadata construction (`MetaPrepare`) on a caller's width tape, after stage 1's
`ArbitraryWidthHighPrepareShared`: its private width slot stays blank. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.MetaShared
open IntegerMultBounds IntegerMultBounds.Machine
noncomputable section
variable {a l : ℕ}
open SharedPlacementAlphabet (setTape)

def privateInput : Tapes 19 a := ⟨fun _ => 0,fun _ _ => blank⟩
def privateOutput (q e : ℕ) : Tapes 19 a :=
  setTape (MetaPrepare.output q e []) 0 (fun _ => blank) 0

def program (focus : Fin l) (q : ℕ) := Placement.placed
  (MetaPrepare.program (a := a) q)
  (SharedPlacementAlphabet.sharedPlacement focus (0 : Fin 19))
def cleanup (focus : Fin l) := Placement.placed
  (MetaPrepare.cleanupProgram (a := a))
  (SharedPlacementAlphabet.sharedPlacement focus (0 : Fin 19))

theorem strip_input (es : List Bool) :
    setTape (MetaPrepare.input (a := a) es) 0 (fun _ => blank) 0 = privateInput := by
  apply congrArg₂ Tapes.mk <;> apply List.ofFn_injective <;> rfl

theorem strip_output (q e : ℕ) (es : List Bool) :
    setTape (MetaPrepare.output (a := a) q e es) 0 (fun _ => blank) 0 =
      privateOutput q e := by
  apply congrArg₂ Tapes.mk <;> apply List.ofFn_injective <;> rfl

private theorem retained_caller (caller : Tapes l a) (focus : Fin l) (q e : ℕ)
    (es : List Bool) (ht : caller.tape focus = RadixZeroFill.encodedBinary es)
    (hh : caller.head focus = 1) :
    setTape caller focus ((MetaPrepare.output (a := a) q e es).tape 0)
      ((MetaPrepare.output (a := a) q e es).head 0) = caller := by
  change setTape caller focus (RadixZeroFill.encodedBinary es) 1 = caller
  rw [← ht,← hh]
  exact SharedPlacementAlphabet.setTape_self _ _

theorem constructs (focus : Fin l) (caller : Tapes l a) (q e : ℕ)
    (hq : 2 ≤ q) (he : 0 < e) (es : List Bool)
    (hv : Counter.value es = e) (hc : GrowingCounterData.Canonical es)
    (ht : caller.tape focus = RadixZeroFill.encodedBinary es) (hh : caller.head focus = 1) :
    HoareTime (program (a := a) focus q)
      (fun z => z = caller.append privateInput)
      (fun z => z = caller.append (privateOutput q e))
      (MetaPrepare.constant q*MetaPrepare.rounded q e) := by
  have h := SharedPlacementAlphabet.shared_hoare
    (MetaPrepare.construct_hoare (a := a) q e hq he es hv hc)
    caller focus (0 : Fin 19) (fun _ => blank) 0 ht hh
  rw [strip_input,strip_output,retained_caller caller focus q e es ht hh] at h
  exact h

theorem cleans (focus : Fin l) (caller : Tapes l a) (q e : ℕ)
    (hq : 2 ≤ q) (es : List Bool)
    (ht : caller.tape focus = RadixZeroFill.encodedBinary es) (hh : caller.head focus = 1) :
    HoareTime (cleanup (a := a) focus)
      (fun z => z = caller.append (privateOutput q e))
      (fun z => z = caller.append privateInput) (45*MetaPrepare.rounded q e) := by
  have h := SharedPlacementAlphabet.shared_hoare
    (MetaPrepare.cleanup_hoare (a := a) q e hq es)
    caller focus (0 : Fin 19) (fun _ => blank) 0 ht hh
  have hr : setTape caller focus ((MetaPrepare.input (a := a) es).tape 0)
      ((MetaPrepare.input (a := a) es).head 0) = caller := by
    change setTape caller focus (RadixZeroFill.encodedBinary es) 1 = caller
    rw [← ht,← hh]
    exact SharedPlacementAlphabet.setTape_self _ _
  rw [strip_output,strip_input,hr] at h
  exact h

theorem private_output_width (q e : ℕ) :
    (privateOutput (a := a) q e).head 0 = 0 ∧
    (privateOutput (a := a) q e).tape 0 = fun _ => blank := ⟨rfl,rfl⟩

theorem private_output_headers (q e : ℕ) (i : Fin 5) :
    (privateOutput (a := a) q e).head (MetaPrepare.slots i) = 1 ∧
    (privateOutput (a := a) q e).tape (MetaPrepare.slots i) =
      RadixZeroFill.encodedBinary (MetaPrepare.words q e i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem private_output_blank (q e : ℕ) (i : Fin 19)
    (hi : i.val = 0 ∨ i.val = 2 ∨ 7 ≤ i.val) :
    (privateOutput (a := a) q e).head i = 0 ∧
    (privateOutput (a := a) q e).tape i = fun _ => blank := by
  fin_cases i <;> first | exact ⟨rfl,rfl⟩ | norm_num at hi

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.MetaShared
