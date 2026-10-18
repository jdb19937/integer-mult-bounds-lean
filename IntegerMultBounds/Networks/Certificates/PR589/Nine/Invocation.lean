module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.StreamFrames
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortLabels
public import IntegerMultBounds.Networks.Certificates.PR589.FramedDirty

/-!
# One invocation of the word in its window

At stage `n` the word runs in window coordinates: a register whose local frame is the label `i`
is stored in the exchange frame of `windowProj n Pᵢ = Pᵢ ⊕ lower n`, the exterior blocks `0, …, n - 1`
exchanged.

* **Forward** (`forwardFrame`): `Framed.execute` on these frames. On arbitrary dirty registers,
  `forward_source`, `forward_target` and `forward_helper` give each register's output: a source
  changes from frame `P` to `1`, a target from `0` to `1 - P` and receives its source, a helper
  changes from `0` to `1`. Every higher register ends at zero (`forward_high`).
* **Reverse** (`reverseFrame`): the reflected frames `(1 - Pᵢ) ⊕ lower n`. `reverseRun` is the
  inverse of `Framed.execute` on them (`reverseRun_execute`, `execute_reverseRun`), the reflected
  call that reverses the word's chronology. `reverse_source`, `reverse_target` and
  `reverse_helper`: a source changes from `0` to `1 - P`, a target from `P` to `1` and receives its
  source, a helper changes from `0` to `1`.

So in both orientations the side in frames `P → 1` and the side in frames `0 → 1 - P` follow the
stage boundary identities of `Stage`, and the receiving side is the target in forward and the
source in reverse.
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Nine

open Matrix
open Frames (initialRefs finalRefs)

/-- The matrix of a label's orthogonal projector. -/
noncomputable def labelProj (i : ℕ) : Matrix (Fin 8) (Fin 8) ℚ :=
  LinearMap.toMatrix' (Geometry.projector i)

theorem projector_comp_self (i : ℕ) :
    (Geometry.projector i).comp (Geometry.projector i) = Geometry.projector i := by
  rw [Geometry.projector, ProjectionTrace.projector_eq _ _ _ (Geometry.restrict_nondegenerate _)]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply]
  exact ProjectionRank.project_left Geometry.form Geometry.form_symm (Geometry.label i)
    (Geometry.restrict_nondegenerate _)
    (ProjectionRank.project_mem Geometry.form Geometry.form_symm _ (Geometry.restrict_nondegenerate _) x)

theorem labelProj_mul_self (i : ℕ) : labelProj i * labelProj i = labelProj i := by
  rw [labelProj, ← LinearMap.toMatrix'_comp, projector_comp_self]

theorem one_sub_labelProj_mul_self (i : ℕ) :
    (1 - labelProj i) * (1 - labelProj i) = 1 - labelProj i := by
  rw [sub_mul, mul_sub, mul_sub, labelProj_mul_self, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul]
  abel

theorem lower_mul_self (n : ℕ) : lower n * lower n = lower n := by
  rw [lower, diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> simp

/-- A local frame with the exterior blocks `0, …, n - 1` exchanged. -/
def windowProj (n : ℕ) (U : Matrix (Fin 8) (Fin 8) ℚ) : Matrix Axis Axis ℚ := fromBlocks U 0 0 (lower n)

theorem windowProj_mul_self (n : ℕ) {U : Matrix (Fin 8) (Fin 8) ℚ} (hU : U * U = U) :
    windowProj n U * windowProj n U = windowProj n U := by
  rw [windowProj, fromBlocks_multiply, hU, lower_mul_self]
  simp

noncomputable def forwardFrame (n i : ℕ) : FramedCircuit.Frame (ZMod 2) Stream :=
  exchangeFrame (windowProj n (labelProj i)) (windowProj_mul_self n (labelProj_mul_self i))

noncomputable def reverseFrame (n i : ℕ) : FramedCircuit.Frame (ZMod 2) Stream :=
  exchangeFrame (windowProj n (1 - labelProj i))
    (windowProj_mul_self n (one_sub_labelProj_mul_self i))

/-! ### The projectors of the port registers -/

theorem labelProj_toLin' (i : ℕ) (M : Matrix (Fin 8) (Fin 8) ℚ)
    (h : Geometry.projector i = Matrix.toLin' M) : labelProj i = M := by
  rw [labelProj, h, LinearMap.toMatrix'_toLin']

theorem labelProj_source_initial (t : ℕ) (ht : t < 111) :
    labelProj (initialRefs t) = (port t).lineProj :=
  labelProj_toLin' _ _ (projector_source_initial t ht)

theorem labelProj_source_final (t : ℕ) (ht : t < 111) : labelProj (finalRefs t) = 1 := by
  apply labelProj_toLin'
  rw [projector_source_final t ht, Matrix.toLin'_one]

theorem labelProj_target_initial (t : ℕ) (ht : t < 111) : labelProj (initialRefs (111 + t)) = 0 := by
  apply labelProj_toLin'
  rw [projector_target_initial t ht, map_zero]

theorem labelProj_target_final (t : ℕ) (ht : t < 111) :
    labelProj (finalRefs (111 + t)) = 1 - (port t).lineProj :=
  labelProj_toLin' _ _ (projector_target_final t ht)

theorem helper_refs : ∀ h < 439, initialRefs (222 + h) = 0 ∧ finalRefs (222 + h) = 1 := by
  decide +kernel

theorem labelProj_zero : labelProj 0 = 0 := by
  apply labelProj_toLin'
  rw [Geometry.projector_zero, map_zero]

theorem labelProj_one : labelProj 1 = 1 := by
  have h := labelProj_source_final 0 (by norm_num)
  rwa [(source_frames 0 (by norm_num)).2.2] at h

/-! ### The word's dirty endpoint -/

/-- The word's dirty endpoint on stored values: every target receives its source. -/
def wordEndpoint {E : Type*} [AddCommGroup E] (stored : Fin 661 → E) (i : Fin 661) : E :=
  if hi : 111 ≤ i.val ∧ i.val < 222 then stored i + stored ⟨i.val - 111, by omega⟩ else stored i

theorem wordEndpoint_involutive {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (stored : Fin 661 → E) : wordEndpoint (wordEndpoint stored) = stored := by
  funext i
  simp only [wordEndpoint]
  by_cases hi : 111 ≤ i.val ∧ i.val < 222
  · have hs : ¬(111 ≤ i.val - 111 ∧ i.val - 111 < 222) := by omega
    simp only [hi, hs, and_self, dite_true, dite_false]
    have h2 : ∀ x : E, x + x = 0 := fun x => by
      rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [add_assoc, h2, add_zero]
  · simp [hi]

/-- The stored values of a register vector in a frame profile. -/
noncomputable def storedIn (frames : ℕ → FramedCircuit.Frame (ZMod 2) Stream) (v : ℕ → Stream) :
    Fin 661 → Stream := fun j => (frames (Frames.snapshot initialRefs j.val)).symm (v j.val)

theorem encode_storedIn (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) Stream) (v : ℕ → Stream)
    (hv : ∀ j, 661 ≤ j → v j = 0) :
    FramedCircuit.encode (fun j => frameOf (Frames.snapshot initialRefs j))
        (Copy.extendStored (storedIn frameOf v)) = v := by
  funext j
  simp only [FramedCircuit.encode, Copy.extendStored, storedIn]
  by_cases hj : j < 661
  · simp [hj]
  · simp [hj, hv j (by omega)]

/-- The framed word on dirty registers, register by register. -/
theorem execute_registers (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) Stream) (v : ℕ → Stream)
    (hv : ∀ j, 661 ≤ j → v j = 0) (i : Fin 661) :
    Framed.execute frameOf v i.val =
      frameOf (finalRefs i.val) (wordEndpoint (storedIn frameOf v) i) := by
  conv_lhs => rw [← encode_storedIn frameOf v hv]
  rw [Framed.execute_dirty]
  rfl

theorem execute_high_registers (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) Stream) (v : ℕ → Stream)
    (hv : ∀ j, 661 ≤ j → v j = 0) (j : ℕ) (hj : 661 ≤ j) : Framed.execute frameOf v j = 0 := by
  rw [← encode_storedIn frameOf v hv]
  exact Framed.execute_high frameOf _ j hj

/-! ### Forward -/

section Forward

variable (n : ℕ) (v : ℕ → Stream) (hv : ∀ j, 661 ≤ j → v j = 0)
include hv

theorem forward_source (t : ℕ) (ht : t < 111) :
    Framed.execute (forwardFrame n) v t =
      along (exchange (windowProj n (port t).lineProj) * exchange (windowProj n 1)) (v t) := by
  have h := execute_registers (forwardFrame n) v hv ⟨t, by omega⟩
  simp only [wordEndpoint, show ¬(111 ≤ t ∧ t < 222) by omega, dite_false, storedIn,
    Frames.snapshot, show t < 661 by omega, ite_true] at h
  rw [h, forwardFrame, forwardFrame, exchangeFrame_change, labelProj_source_initial t ht,
    labelProj_source_final t ht]

theorem forward_target (t : ℕ) (ht : t < 111) :
    Framed.execute (forwardFrame n) v (111 + t) =
      along (exchange (windowProj n 0) * exchange (windowProj n (1 - (port t).lineProj)))
          (v (111 + t)) +
        along (exchange (windowProj n (port t).lineProj) *
          exchange (windowProj n (1 - (port t).lineProj))) (v t) := by
  have h := execute_registers (forwardFrame n) v hv ⟨111 + t, by omega⟩
  simp only [wordEndpoint, show 111 ≤ 111 + t ∧ 111 + t < 222 by omega, and_self, dite_true,
    storedIn, Frames.snapshot, show 111 + t < 661 by omega, show 111 + t - 111 = t by omega,
    show t < 661 by omega, ite_true] at h
  rw [h, map_add, forwardFrame, forwardFrame, forwardFrame, exchangeFrame_change,
    exchangeFrame_change, labelProj_target_initial t ht, labelProj_target_final t ht,
    labelProj_source_initial t ht]

theorem forward_helper (h : ℕ) (hh : h < 439) :
    Framed.execute (forwardFrame n) v (222 + h) =
      along (exchange (windowProj n 0) * exchange (windowProj n 1)) (v (222 + h)) := by
  have he := execute_registers (forwardFrame n) v hv ⟨222 + h, by omega⟩
  simp only [wordEndpoint, show ¬(111 ≤ 222 + h ∧ 222 + h < 222) by omega, dite_false, storedIn,
    Frames.snapshot, show 222 + h < 661 by omega, ite_true] at he
  rw [he, forwardFrame, forwardFrame, exchangeFrame_change, (helper_refs h hh).1,
    (helper_refs h hh).2, labelProj_zero, labelProj_one]

theorem forward_high (j : ℕ) (hj : 661 ≤ j) : Framed.execute (forwardFrame n) v j = 0 :=
  execute_high_registers _ v hv j hj

end Forward

/-! ### Reverse -/

/-- The reflected call: the inverse of the framed word on the reflected frames. -/
noncomputable def reverseRun (n : ℕ) (y : ℕ → Stream) : ℕ → Stream :=
  FramedCircuit.encode (fun j => reverseFrame n (Frames.snapshot initialRefs j))
    (Copy.extendStored (wordEndpoint fun j : Fin 661 => (reverseFrame n (finalRefs j.val)).symm (y j.val)))

theorem reverseRun_execute (n : ℕ) (x : ℕ → Stream) (hx : ∀ j, 661 ≤ j → x j = 0) :
    reverseRun n (Framed.execute (reverseFrame n) x) = x := by
  have hout : (fun j : Fin 661 => (reverseFrame n (finalRefs j.val)).symm
      (Framed.execute (reverseFrame n) x j.val)) = wordEndpoint (storedIn (reverseFrame n) x) := by
    funext j
    rw [execute_registers _ x hx j, LinearEquiv.symm_apply_apply]
  rw [reverseRun, hout, wordEndpoint_involutive, encode_storedIn _ x hx]

theorem execute_reverseRun (n : ℕ) (y : ℕ → Stream) (hy : ∀ j, 661 ≤ j → y j = 0) :
    Framed.execute (reverseFrame n) (reverseRun n y) = y := by
  funext j
  by_cases hj : j < 661
  · have hstored : storedIn (reverseFrame n) (reverseRun n y) =
        wordEndpoint fun i : Fin 661 => (reverseFrame n (finalRefs i.val)).symm (y i.val) := by
      funext i
      simp [storedIn, reverseRun, FramedCircuit.encode, Copy.extendStored, i.isLt]
    have hz : ∀ k, 661 ≤ k → reverseRun n y k = 0 := by
      intro k hk
      simp [reverseRun, FramedCircuit.encode, Copy.extendStored, show ¬k < 661 by omega]
    rw [show j = (⟨j, hj⟩ : Fin 661).val from rfl, execute_registers _ _ hz, hstored,
      wordEndpoint_involutive, LinearEquiv.apply_symm_apply]
  · have hz : ∀ k, 661 ≤ k → reverseRun n y k = 0 := by
      intro k hk
      simp [reverseRun, FramedCircuit.encode, Copy.extendStored, show ¬k < 661 by omega]
    rw [execute_high_registers _ _ hz j (by omega), hy j (by omega)]

section Reverse

variable (n : ℕ) (y : ℕ → Stream)

theorem reverse_source (t : ℕ) (ht : t < 111) :
    reverseRun n y t =
      along (exchange (windowProj n 0) * exchange (windowProj n (1 - (port t).lineProj))) (y t) := by
  simp only [reverseRun, FramedCircuit.encode, Copy.extendStored, show t < 661 by omega,
    dite_true, Frames.snapshot, ite_true, wordEndpoint, show ¬(111 ≤ t ∧ t < 222) by omega,
    dite_false]
  rw [reverseFrame, reverseFrame, exchangeFrame_change, labelProj_source_final t ht,
    labelProj_source_initial t ht, sub_self]

theorem reverse_target (t : ℕ) (ht : t < 111) :
    reverseRun n y (111 + t) =
      along (exchange (windowProj n (port t).lineProj) * exchange (windowProj n 1)) (y (111 + t)) +
        along (exchange (windowProj n 0) * exchange (windowProj n 1)) (y t) := by
  simp only [reverseRun, FramedCircuit.encode, Copy.extendStored, show 111 + t < 661 by omega,
    dite_true, Frames.snapshot, ite_true, wordEndpoint, show 111 ≤ 111 + t ∧ 111 + t < 222 by omega,
    and_self, show 111 + t - 111 = t by omega]
  rw [map_add, reverseFrame, reverseFrame, reverseFrame, exchangeFrame_change, exchangeFrame_change,
    labelProj_target_final t ht, labelProj_target_initial t ht, labelProj_source_final t ht,
    sub_sub_cancel, sub_zero, sub_self]

theorem reverse_helper (h : ℕ) (hh : h < 439) :
    reverseRun n y (222 + h) =
      along (exchange (windowProj n 0) * exchange (windowProj n 1)) (y (222 + h)) := by
  simp only [reverseRun, FramedCircuit.encode, Copy.extendStored, show 222 + h < 661 by omega,
    dite_true, Frames.snapshot, ite_true, wordEndpoint, show ¬(111 ≤ 222 + h ∧ 222 + h < 222) by omega,
    dite_false]
  rw [reverseFrame, reverseFrame, exchangeFrame_change, (helper_refs h hh).1, (helper_refs h hh).2,
    labelProj_zero, labelProj_one, sub_self, sub_zero]

theorem reverse_high (j : ℕ) (hj : 661 ≤ j) : reverseRun n y j = 0 := by
  simp [reverseRun, FramedCircuit.encode, Copy.extendStored, show ¬j < 661 by omega]

end Reverse

end IntegerMultBounds.Networks.Certificates.PR589.Nine
