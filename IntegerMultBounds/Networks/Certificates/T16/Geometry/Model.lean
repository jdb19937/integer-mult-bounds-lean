module

public import IntegerMultBounds.Networks.Labels
public import IntegerMultBounds.Networks.BinaryScalarReplay
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Model
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Finite binary label geometry only. No ambient operator, scalar endpoint,
or physical hosting is specified by these certificates. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

abbrev F := ZMod 2
abbrev Address := Fin 9 → F
abbrev Mask := BitVec 9

def decode (mask : Mask) : Address := fun i => if mask.getLsbD i.val then 1 else 0

@[simp] theorem decode_zero : decode 0 = 0 := by ext i; simp [decode]

theorem decode_xor (a b : Mask) : decode (a ^^^ b) = decode a + decode b := by
  ext i
  simp only [decode, BitVec.getLsbD_xor, Pi.add_apply]
  cases a.getLsbD i.val <;> cases b.getLsbD i.val <;> simp [CharTwo.add_self_eq_zero]

structure Frame where
  rank : ℕ
  masks : Fin rank → Mask
  dual : Fin rank → Mask

def Frame.vectors (f : Frame) : Fin f.rank → Address := fun i => decode (f.masks i)
def Frame.space (f : Frame) : Submodule F Address := Submodule.span F (Set.range f.vectors)

def Frame.DualCheck (f : Frame) : Prop :=
  ∀ i j, Labels.binary 9 (decode (f.dual i)) (f.vectors j) = if i = j then 1 else 0

instance (f : Frame) : Decidable f.DualCheck := inferInstanceAs
  (Decidable (∀ i j, Labels.binary 9 (decode (f.dual i)) (f.vectors j) = if i = j then 1 else 0))

theorem Frame.independent (f : Frame) (h : f.DualCheck) : LinearIndependent F f.vectors := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one f.vectors
    (fun i => Labels.binary 9 (decode (f.dual i)))
  · intro i j hij
    simpa [hij] using h i j
  · intro i
    simpa using h i i

theorem Frame.dimension (f : Frame) (h : LinearIndependent F f.vectors) :
    Module.finrank F f.space = f.rank := by
  unfold Frame.space
  exact (finrank_span_eq_card h).trans (Fintype.card_fin _)

/-- A literal XOR combination of the supplied masks. -/
def combine : List Mask → ℕ → Mask
  | [], _ => 0
  | m :: ms, selection => (if selection % 2 = 1 then m else 0) ^^^ combine ms (selection / 2)

theorem combine_mem (W : Submodule F Address) (ms : List Mask)
    (hm : ∀ m ∈ ms, decode m ∈ W) (selection : ℕ) : decode (combine ms selection) ∈ W := by
  induction ms generalizing selection with
  | nil =>
    change decode (0 : Mask) ∈ W
    rw [decode_zero]
    exact W.zero_mem
  | cons m ms ih =>
    rw [combine, decode_xor]
    apply W.add_mem
    · split_ifs
      · exact hm m (List.mem_cons_self ..)
      · rw [decode_zero]
        exact W.zero_mem
    · exact ih (fun m h => hm m (List.mem_cons_of_mem _ h)) _

def Frame.CombinationCheck (a b : Frame) (witness : Fin a.rank → ℕ) : Prop :=
  ∀ i, a.masks i = combine (List.ofFn b.masks) (witness i)

instance (a b : Frame) (witness : Fin a.rank → ℕ) :
    Decidable (a.CombinationCheck b witness) := inferInstanceAs
  (Decidable (∀ i, a.masks i = combine (List.ofFn b.masks) (witness i)))

theorem Frame.inclusion (a b : Frame) (witness : Fin a.rank → ℕ)
    (h : a.CombinationCheck b witness) : a.space ≤ b.space := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change decode (a.masks i) ∈ b.space
  rw [h i]
  apply combine_mem
  intro m hm
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
  exact Submodule.subset_span ⟨j, rfl⟩

structure CertifiedFrame where
  data : Frame
  independent : LinearIndependent F data.vectors

abbrev CertifiedFrame.space (f : CertifiedFrame) := f.data.space

theorem CertifiedFrame.dimension (f : CertifiedFrame) :
    Module.finrank F f.space = f.data.rank := f.data.dimension f.independent

end IntegerMultBounds.Networks.Certificates.T16.Geometry
