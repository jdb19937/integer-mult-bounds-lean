module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# Selective coordinate shears with borrowed controls

The logical address contract for arbitrary-source routing. Sources lie outside the
selected targets, but need not be contiguous or ordered before them. The four-pass
borrowed-control construction restores arbitrary control contents. These are address
identities, not a packed modular implementation or a tape-time bound.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {ι : Type*} [DecidableEq ι]

/-- Toggle only selected address bits, using one control bit per coordinate. -/
def toggle (targets : Finset ι) (control x : ι → Bool) : ι → Bool :=
  fun i => if i ∈ targets then Bool.xor (x i) (control i) else x i

@[simp] theorem toggle_off (targets : Finset ι) (control x : ι → Bool)
    {i : ι} (hi : i ∉ targets) : toggle targets control x i = x i := by
  simp [toggle, hi]

/-- Every source coordinate survives a selective toggle. -/
theorem toggle_source (targets : Finset ι) (source : ι → ι)
    (hsource : ∀ i ∈ targets, source i ∉ targets) (control x : ι → Bool)
    {i : ι} (hi : i ∈ targets) :
    toggle targets control x (source i) = x (source i) :=
  toggle_off targets control x (hsource i hi)

/-- The ideal simultaneous XOR from arbitrary source coordinates. -/
def shear (targets : Finset ι) (source : ι → ι) (x : ι → Bool) : ι → Bool :=
  toggle targets (fun i => x (source i)) x

theorem shear_involutive (targets : Finset ι) (source : ι → ι)
    (hsource : ∀ i ∈ targets, source i ∉ targets) :
    Function.Involutive (shear targets source) := by
  intro x
  funext i
  by_cases hi : i ∈ targets
  · simp only [shear, toggle, hi, ite_true, hsource i hi, ite_false]
    cases x i <;> cases x (source i) <;> rfl
  · simp [shear, toggle, hi]

/-- In particular the ideal routing step is a permutation on all addresses. -/
def shearPerm (targets : Finset ι) (source : ι → ι)
    (hsource : ∀ i ∈ targets, source i ∉ targets) : Equiv.Perm (ι → Bool) where
  toFun := shear targets source
  invFun := shear targets source
  left_inv := shear_involutive targets source hsource
  right_inv := shear_involutive targets source hsource

/-- Load selected source bits into borrowed controls by XOR; other controls stay put. -/
def load (targets : Finset ι) (source : ι → ι) (x control : ι → Bool) : ι → Bool :=
  fun i => if i ∈ targets then Bool.xor (control i) (x (source i)) else control i

/-- Toggle, load, toggle, unload. The unload reads the actual final data. -/
def borrowedShear (targets : Finset ι) (source : ι → ι)
    (x control : ι → Bool) : (ι → Bool) × (ι → Bool) :=
  let x₁ := toggle targets control x
  let control₁ := load targets source x₁ control
  let x₂ := toggle targets control₁ x₁
  (x₂, load targets source x₂ control₁)

/-- The source reads during the two loads agree even when the controls are dirty. -/
theorem load_toggle (targets : Finset ι) (source : ι → ι)
    (hsource : ∀ i ∈ targets, source i ∉ targets) (x control mask : ι → Bool) :
    load targets source (toggle targets mask x) control = load targets source x control := by
  funext i
  by_cases hi : i ∈ targets
  · simp [load, hi, toggle_source targets source hsource mask x hi]
  · simp [load, hi]

/-- The two toggles cancel the borrowed control and keep precisely the source bit. -/
theorem toggle_load_toggle (targets : Finset ι) (source : ι → ι)
    (x control : ι → Bool) :
    toggle targets (load targets source x control) (toggle targets control x) =
      shear targets source x := by
  funext i
  by_cases hi : i ∈ targets
  · simp only [toggle, load, shear, hi, ite_true]
    cases x i <;> cases control i <;> cases x (source i) <;> rfl
  · simp [toggle, shear, hi]

/-- Every data and borrowed-control coordinate has its exact final value. -/
theorem borrowedShear_eq (targets : Finset ι) (source : ι → ι)
    (hsource : ∀ i ∈ targets, source i ∉ targets) (x control : ι → Bool) :
    borrowedShear targets source x control = (shear targets source x, control) := by
  dsimp only [borrowedShear]
  simp only [load_toggle targets source hsource]
  rw [toggle_load_toggle]
  congr 1
  funext i
  by_cases hi : i ∈ targets
  · simp only [load, hi, ite_true]
    cases control i <;> cases x (source i) <;> rfl
  · simp [load, hi]

end IntegerMultBounds.MathlibTM2.Routing
