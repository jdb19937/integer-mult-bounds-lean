module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Data.Finset.Max
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirSchedule

/-!
# Computable cycle reflections

Each orbit is based at its least coordinate. Bounded orbit traversal finds that
base, and a terminating search finds its exponent. Negating the exponent gives
one reflection; composing with the permutation gives the other. Tape execution
and its generation cost are separate obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

omit [DecidableEq ι] [LinearOrder ι] in
private theorem sameCycle_bounded (f : Equiv.Perm ι) (x y : ι) :
    f.SameCycle x y ↔ ∃ i : Fin (Fintype.card ι), (f ^ i.val) x = y := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    let p := Function.minimalPeriod f x
    have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts
      (f.injective.mem_periodicPts x)
    refine ⟨⟨n % p, lt_of_lt_of_le (Nat.mod_lt n hp) Function.minimalPeriod_le_card⟩, ?_⟩
    rw [Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq]
    simpa only [Equiv.Perm.coe_pow] using hn
  · rintro ⟨i, hi⟩
    exact ⟨i.val, by simpa using hi⟩

def permutationOrbit (f : Equiv.Perm ι) (x : ι) : Finset ι :=
  Finset.univ.filter fun y => ∃ i : Fin (Fintype.card ι), (f ^ i.val) x = y

omit [LinearOrder ι] in
@[simp] theorem mem_permutationOrbit (f : Equiv.Perm ι) (x y : ι) :
    y ∈ permutationOrbit f x ↔ f.SameCycle x y := by
  simp only [permutationOrbit, Finset.mem_filter, Finset.mem_univ, true_and,
    ← sameCycle_bounded]

omit [LinearOrder ι] in
theorem permutationOrbit_nonempty (f : Equiv.Perm ι) (x : ι) :
    (permutationOrbit f x).Nonempty := ⟨x, (mem_permutationOrbit f x x).mpr (.refl f x)⟩

def permutationBase (f : Equiv.Perm ι) (x : ι) : ι :=
  (permutationOrbit f x).min' (permutationOrbit_nonempty f x)

theorem permutationBase_sameCycle (f : Equiv.Perm ι) (x : ι) :
    f.SameCycle x (permutationBase f x) :=
  (mem_permutationOrbit f x _).mp (Finset.min'_mem _ _)

theorem permutationBase_eq (f : Equiv.Perm ι) {x y : ι} (h : f.SameCycle x y) :
    permutationBase f x = permutationBase f y := by
  have he : permutationOrbit f x = permutationOrbit f y := by
    ext z
    simp only [mem_permutationOrbit]
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩
  unfold permutationBase
  congr 1

theorem permutationExponent_exists (f : Equiv.Perm ι) (x : ι) :
    ∃ n : ℕ, (f ^ n) (permutationBase f x) = x :=
  (permutationBase_sameCycle f x).symm.exists_nat_pow_eq

def permutationExponent (f : Equiv.Perm ι) (x : ι) : ℕ :=
  Nat.find (permutationExponent_exists f x)

theorem permutationExponent_spec (f : Equiv.Perm ι) (x : ι) :
    (f ^ permutationExponent f x) (permutationBase f x) = x :=
  Nat.find_spec (permutationExponent_exists f x)

/-- The terminating exponent search needs fewer than one full coordinate count. -/
theorem permutationExponent_lt_card (f : Equiv.Perm ι) (x : ι) :
    permutationExponent f x < Fintype.card ι := by
  obtain ⟨i, hi⟩ := (sameCycle_bounded f (permutationBase f x) x).mp
    (permutationBase_sameCycle f x).symm
  exact lt_of_le_of_lt (Nat.find_min' (permutationExponent_exists f x) hi) i.isLt

def permutationReflection (f : Equiv.Perm ι) (x : ι) : ι :=
  (f ^ (-(permutationExponent f x : ℤ))) (permutationBase f x)

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
private theorem inverse_exponents (f : Equiv.Perm ι) (x : ι) (a b : ℤ)
    (h : (f ^ a) x = (f ^ b) x) : (f ^ (-a)) x = (f ^ (-b)) x := by
  have he := congrArg (fun y => (f ^ (-a - b)) y) h.symm
  simp only [← Equiv.Perm.mul_apply, ← zpow_add] at he
  convert he using 1 <;> congr 2 <;> omega

theorem permutationReflection_orbit (f : Equiv.Perm ι) (x : ι) (z : ℤ) :
    permutationReflection f ((f ^ z) (permutationBase f x)) =
      (f ^ (-z)) (permutationBase f x) := by
  let y := (f ^ z) (permutationBase f x)
  have hy : f.SameCycle x y := (permutationBase_sameCycle f x).zpow_right
  have hb := (permutationBase_eq f hy).symm
  have he := permutationExponent_spec f y
  rw [hb, ← zpow_natCast] at he
  change (f ^ (-(permutationExponent f y : ℤ))) (permutationBase f y) = _
  rw [hb]
  exact inverse_exponents f (permutationBase f x) _ z he

theorem permutationReflection_involutive (f : Equiv.Perm ι) :
    Function.Involutive (permutationReflection f) := by
  intro x
  change permutationReflection f ((f ^ (-(permutationExponent f x : ℤ)))
    (permutationBase f x)) = x
  rw [permutationReflection_orbit]
  simpa using permutationExponent_spec f x

theorem permutationReflection_apply (f : Equiv.Perm ι) (x : ι) :
    permutationReflection f (f x) = f.symm (permutationReflection f x) := by
  have hx : f x = (f ^ ((permutationExponent f x : ℤ) + 1)) (permutationBase f x) := by
    rw [add_comm, zpow_add, Equiv.Perm.mul_apply, zpow_one, zpow_natCast,
      permutationExponent_spec]
  rw [hx, permutationReflection_orbit]
  change (f ^ (-((permutationExponent f x : ℤ) + 1))) (permutationBase f x) =
    (f⁻¹ * f ^ (-(permutationExponent f x : ℤ))) (permutationBase f x)
  rw [← zpow_neg_one, ← zpow_add]
  congr 2
  omega

/-- Every coordinate permutation is the composition of two explicit matchings. -/
theorem permutation_two_matchings (f : Equiv.Perm ι) :
    Function.Involutive (permutationReflection f) ∧
      Function.Involutive (fun x => f (permutationReflection f x)) ∧
      ∀ x, f (permutationReflection f (permutationReflection f x)) = f x := by
  have hi := permutationReflection_involutive f
  refine ⟨hi, ?_, fun x => congrArg f (hi x)⟩
  intro x
  change f (permutationReflection f (f (permutationReflection f x))) = x
  rw [permutationReflection_apply, hi, f.apply_symm_apply]

/-- Eighteen directional shears for any coordinate permutation. Their reservoir
safety follows class by class from `reservoirPass_targets_avoid`; physical
placement, sparse-profile compilation and executed setup are still required. -/
def permutationReservoirSchedule (banks : Fin 3 → Finset ι) (f : Equiv.Perm ι)
    (x : ι → Bool) : ι → Bool :=
  reservoirSchedule banks (permutationReflection f)
    (reservoirSchedule banks (fun i => f (permutationReflection f i)) x)

theorem permutationReservoirSchedule_eq (banks : Fin 3 → Finset ι)
    (f : Equiv.Perm ι) (x : ι → Bool) :
    permutationReservoirSchedule banks f x = fun i => x (f i) := by
  obtain ⟨hi, hj, hcomp⟩ := permutation_two_matchings f
  simp only [permutationReservoirSchedule, reservoirSchedule_eq banks _ hi,
    reservoirSchedule_eq banks _ hj]
  funext i
  exact congrArg x (hcomp i)

end IntegerMultBounds.MathlibTM2.Routing
