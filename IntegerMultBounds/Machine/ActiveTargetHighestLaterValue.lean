module

public import IntegerMultBounds.Machine.BinaryPackedFieldSwap
public import IntegerMultBounds.Machine.ActiveTargetHighestValue

/-! Exact conjugation for a highest target bit preceding its source. The two
one-bit fields are exchanged physically by the eventual caller machine. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActiveTargetHighestLaterValue
noncomputable section
open RadixRangePadding (volume index coordinates transpose)
variable {P G B : ℕ} {α : Type*}

def xorBit (a b : Fin 2) : Fin 2 := ⟨(a.val+b.val)%2,Nat.mod_lt _ (by decide)⟩
theorem xorBit_twice (a b : Fin 2) : xorBit (xorBit a b) b=a := by
  fin_cases a <;> fin_cases b <;> rfl

def earlier (x : Fin (volume P 2 G B) → α) : Fin (volume P 2 G B) → α := fun z =>
  let c := coordinates z
  x (index c.1 c.2.1 c.2.2.1 (xorBit c.2.2.2.1 c.2.1) c.2.2.2.2)
def later (x : Fin (volume P 2 G B) → α) : Fin (volume P 2 G B) → α := fun z =>
  let c := coordinates z
  x (index c.1 (xorBit c.2.1 c.2.2.2.1) c.2.2.1 c.2.2.2.1 c.2.2.2.2)

theorem conjugation (x : Fin (volume P 2 G B) → α) :
    transpose (earlier (transpose x))=later x := by
  funext z
  simp only [transpose,earlier,later,RadixRangePadding.coordinates_index]

theorem later_entry (x : Fin (volume P 2 G B) → α) (p : Fin P)
    (target source : Fin 2) (g : Fin G) (j : Fin B) :
    later x (index p (xorBit target source) g source j)=x (index p target g source j) := by
  simp only [later,RadixRangePadding.coordinates_index,xorBit_twice]

theorem earlier_entry (x : Fin (volume P 2 G B) → α) (p : Fin P)
    (source target : Fin 2) (g : Fin G) (j : Fin B) :
    earlier x (index p source g (xorBit target source) j)=x (index p source g target j) := by
  simp only [earlier,RadixRangePadding.coordinates_index,xorBit_twice]

theorem prefix_eq (G L : ℕ) : ActiveTargetHighestRun.prefixSize G L=2^L*2*2^G := by
  change 2^(G+(1+L))=2^L*2*2^G
  rw [pow_add,pow_add,pow_one]
  ring

theorem size_eq (G L B : ℕ) : ActiveTargetHighestRun.volume G L B=volume (2^L) 2 (2^G) B := by
  change ActiveTargetHighestRun.prefixSize G L*(2*B)=_
  rw [prefix_eq]
  unfold volume
  ring

def prefixIndex (G L : ℕ) (p : Fin (2^L)) (s : Fin 2) (g : Fin (2^G)) :
    Fin (ActiveTargetHighestRun.prefixSize G L) :=
  Fin.cast (prefix_eq G L).symm (RecursiveInterchangeRows.pack (RecursiveInterchangeRows.pack p s) g)

theorem prefixIndex_val (G L : ℕ) (p : Fin (2^L)) (s : Fin 2) (g : Fin (2^G)) :
    (prefixIndex G L p s g).val=(p.val*2+s.val)*2^G+g.val := by
  simp only [prefixIndex,Fin.val_cast,RecursiveInterchangeRows.pack_val]


end
end IntegerMultBounds.Machine.ActiveTargetHighestLaterValue
