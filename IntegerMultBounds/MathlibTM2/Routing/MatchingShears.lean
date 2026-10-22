module

public import IntegerMultBounds.MathlibTM2.Routing.Shear
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic

/-!
# A coordinate matching is three selective XORs

Orient each nontrivial edge once. The left endpoints and their mates are disjoint;
all other coordinates are fixed. The three directional shears exchange each pair,
with every source outside its own target set, exactly the R1/R2 logical contract.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {ι : Type*} [DecidableEq ι]
variable (mate : ι → ι) (hinv : Function.Involutive mate) (left : Finset ι)

include hinv in
/-- Right endpoints are exactly the mates of the oriented left endpoints. -/
theorem matchingRight_mem (i : ι) : i ∈ left.image mate ↔ mate i ∈ left := by
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
    rw [← he, hinv]
    exact hj
  · intro hi
    exact Finset.mem_image.mpr ⟨mate i, hi, hinv i⟩

theorem matchingLeft_source (separate : Disjoint left (left.image mate)) :
    ∀ i ∈ left, mate i ∉ left := by
  intro i hi hmate
  exact Finset.disjoint_left.mp separate hmate (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

include hinv in
theorem matchingRight_source (separate : Disjoint left (left.image mate)) :
    ∀ i ∈ left.image mate, mate i ∉ left.image mate := by
  intro i hi hmate
  exact Finset.disjoint_left.mp separate ((matchingRight_mem mate hinv left i).mp hi) hmate

def matchingShears (x : ι → Bool) : ι → Bool :=
  shear left mate (shear (left.image mate) mate (shear left mate x))

include hinv in
/-- All sources survive their own shear and the complete three-pass result is
exactly the coordinate permutation, including every unmatched spectator. -/
theorem matchingShears_eq (separate : Disjoint left (left.image mate))
    (cover : ∀ i, i ∉ left → i ∉ left.image mate → mate i = i) (x : ι → Bool) :
    matchingShears mate left x = fun i => x (mate i) := by
  funext i
  have hm (j : ι) : mate (mate j) = j := hinv j
  by_cases hl : i ∈ left
  · have hr : i ∉ left.image mate := fun hi => Finset.disjoint_left.mp separate hl hi
    have hml := matchingLeft_source mate left separate i hl
    have hmr : mate i ∈ left.image mate := Finset.mem_image.mpr ⟨i, hl, rfl⟩
    simp only [matchingShears, shear, toggle, hl, hr, hml, hmr, hm, ite_true, ite_false]
    cases x i <;> cases x (mate i) <;> rfl
  · by_cases hr : i ∈ left.image mate
    · have hml := (matchingRight_mem mate hinv left i).mp hr
      have hmr := matchingRight_source mate hinv left separate i hr
      simp only [matchingShears, shear, toggle, hl, hr, hml, hmr, hm, ite_true, ite_false]
      cases x i <;> cases x (mate i) <;> rfl
    · simp [matchingShears, shear, toggle, hl, hr, cover i hl hr]

section Orientation
variable [Fintype ι] [LinearOrder ι]

/-- Orient each nontrivial edge from its smaller endpoint. -/
def matchingLeft (mate : ι → ι) : Finset ι := Finset.univ.filter fun i => i < mate i

include hinv in
theorem matchingLeft_disjoint : Disjoint (matchingLeft mate) ((matchingLeft mate).image mate) := by
  apply Finset.disjoint_left.mpr
  intro i hi hr
  have hl : i < mate i := (Finset.mem_filter.mp hi).2
  have hm : mate i < i := by
    have hx := (matchingRight_mem mate hinv (matchingLeft mate) i).mp hr
    simpa [matchingLeft, hinv i] using hx
  exact (lt_asymm hl hm)

include hinv in
theorem matchingLeft_covers (i : ι) (hl : i ∉ matchingLeft mate)
    (hr : i ∉ (matchingLeft mate).image mate) : mate i = i := by
  have ha : ¬ i < mate i := by simpa [matchingLeft] using hl
  have hb : ¬ mate i < i := by
    intro hm
    apply hr
    apply (matchingRight_mem mate hinv (matchingLeft mate) i).mpr
    simpa [matchingLeft, hinv i] using hm
  exact le_antisymm (le_of_not_gt ha) (le_of_not_gt hb)

include hinv in
/-- Every finite coordinate involution has an explicit admissible three-shear schedule. -/
theorem matchingShears_involution (x : ι → Bool) :
    matchingShears mate (matchingLeft mate) x = fun i => x (mate i) :=
  matchingShears_eq mate hinv (matchingLeft mate) (matchingLeft_disjoint mate hinv)
    (matchingLeft_covers mate hinv) x
end Orientation

end IntegerMultBounds.MathlibTM2.Routing
