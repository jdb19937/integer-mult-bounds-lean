module

public import IntegerMultBounds.MathlibTM2.M8.BitNetwork
public import IntegerMultBounds.MathlibTM2.M8.ExchangeBound

/-!
# Framed step lists

A framed step list annotates a node with the frame of every wire. A wire in frame `U` stores
its logical stream read through the partial swap of `U`: `stored = ℓ ∘ D_U` (`Encoded`). The
framed steps are:
* `up i A B` and `down i A B`: wire `i` moves between nested frames, physically the exchange
  program of `B − A` (or `A − B`), with `rank (B − A)` interchanges;
* `gate g F`: an XOR gate whose wires are all in frame `F`;
* `reset i`: wire `i` becomes zero;
* `relabel i F`: a zero wire is declared to be in frame `F`, with no physical step.

On streams encoded in the initial frames, the physical run of a valid framed list is the logical
run of its gates and resets, encoded in the final frames (`run_phys`). The partial swaps are
reduced mod `p ^ b` for a prime `p` beyond `coefficientBound`; frames are idempotents of height at
most `10 ^ 4000` (`IsFrame`), so each edge matrix is within `10 ^ 10000` and its exchange program
runs as its partial swap (`edgeAction_program`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.Swap.Modular (reduce Admissible ratMod)

variable {d : ℕ}

/-- Rational matrices on `d` coordinates. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℚ

/-- A frame: an idempotent with entries of height at most `10 ^ 4000`. -/
structure IsFrame (U : Mat d) : Prop where
  idem : U * U = U
  bound : Height.Bounded U (10 ^ 4000)

/-! ### Partial swaps mod a prime power -/

section Swaps
variable {R : Type*} [CommRing R]

/-- Two partial swaps compose to one: `D_X D_Y = D_{X + Y - 2XY}`. -/
theorem exchange_exchange (X Y : Matrix (Fin d) (Fin d) R) (s : Swap.Shear.State (Fin d) R) :
    Exchange.exchange X (Exchange.exchange Y s) = Exchange.exchange (X + Y - 2 • (X * Y)) s := by
  obtain ⟨h, w⟩ := s
  simp only [Exchange.exchange, mulVec_add, mulVec_mulVec]
  refine Prod.ext ?_ ?_
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, sub_mulVec,
      add_mulVec, one_mulVec, two_smul]
    abel
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, sub_mulVec,
      add_mulVec, one_mulVec, two_smul]
    abel

theorem exchange_zero (s : Swap.Shear.State (Fin d) R) : Exchange.exchange 0 s = s := by
  obtain ⟨h, w⟩ := s
  simp [Exchange.exchange]

theorem exchange_involutive {U : Matrix (Fin d) (Fin d) R} (hU : U * U = U) :
    Function.Involutive (Exchange.exchange U) := fun s => by
  rw [exchange_exchange, hU, two_smul, sub_self, exchange_zero]

end Swaps

theorem ratMod_sub (m : ℕ) {x y : ℚ} (hx : x.den.Coprime m) (hy : y.den.Coprime m) :
    ratMod m (x - y) = ratMod m x - ratMod m y :=
  map_sub (Swap.Modular.toZMod m) ⟨x, hx⟩ ⟨y, hy⟩

theorem reduce_sub (m : ℕ) {A B : Mat d} (hA : Admissible m A) (hB : Admissible m B) :
    reduce m (A - B) = reduce m A - reduce m B := by
  ext i j
  exact ratMod_sub m (hA i j) (hB i j)

/-- Small denominators are prime to every power of a larger prime. -/
theorem admissible_of_bounded {U : Mat d} {h p : ℕ} (hU : Height.Bounded U h) (hp : p.Prime)
    (hhp : h < p) (b : ℕ) : Admissible (p ^ b) U := fun i j => by
  apply Nat.Coprime.pow_right
  have hden : (U i j).den < p := lt_of_le_of_lt ((Height.den_le_ht _).trans (hU i j)) hhp
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
    (Nat.not_dvd_of_pos_of_lt (U i j).den_pos hden))

theorem frameBound_lt {p : ℕ} (hp : coefficientBound < p) : 10 ^ 4000 < p := by
  refine lt_of_le_of_lt ?_ hp
  calc (10 : ℕ) ^ 4000 ≤ 16 ^ 4000 := Nat.pow_le_pow_left (by norm_num) _
    _ = 2 ^ 16000 := by rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    _ ≤ coefficientBound := Exchange.le_coefficientBound
        (le_trans (by norm_num : (16000 : ℕ) ≤ 2 ^ 14) (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/-- The partial swap of a frame at modulus `q`, on addresses. -/
def swapAt (q : ℕ) (U : Mat d) : Address d q → Address d q := Exchange.exchange (reduce q U)

section Prime
variable {p : ℕ} (hp : p.Prime) (hpb : coefficientBound < p) (b : ℕ)
include hp hpb

theorem frame_admissible {U : Mat d} (hU : IsFrame U) : Admissible (p ^ b) U :=
  admissible_of_bounded hU.bound hp (frameBound_lt hpb) b

theorem reduce_idem {U : Mat d} (hU : IsFrame U) :
    reduce (p ^ b) U * reduce (p ^ b) U = reduce (p ^ b) U := by
  rw [← Swap.Modular.reduce_mul _ (frame_admissible hp hpb b hU) (frame_admissible hp hpb b hU),
    hU.idem]

theorem swapAt_involutive {U : Mat d} (hU : IsFrame U) : Function.Involutive (swapAt (p ^ b) U) :=
  exchange_involutive (reduce_idem hp hpb b hU)

/-- Moving up: `D_A ∘ D_{B - A} = D_B` for `A ≤ B`. -/
theorem swapAt_up {A B : Mat d} (hA : IsFrame A) (hB : IsFrame B) (hAB : A * B = A)
    (s : Address d (p ^ b)) : swapAt (p ^ b) A (swapAt (p ^ b) (B - A) s) = swapAt (p ^ b) B s := by
  have ha := frame_admissible hp hpb b hA
  have hb := frame_admissible hp hpb b hB
  have hm : reduce (p ^ b) A * reduce (p ^ b) B = reduce (p ^ b) A := by
    rw [← Swap.Modular.reduce_mul _ ha hb, hAB]
  simp only [swapAt]
  rw [exchange_exchange, reduce_sub _ hb ha, Matrix.mul_sub, hm, reduce_idem hp hpb b hA, sub_self,
    smul_zero, sub_zero, add_sub_cancel]

/-- Moving down: `D_A ∘ D_{A - B} = D_B` for `B ≤ A`. -/
theorem swapAt_down {A B : Mat d} (hA : IsFrame A) (hB : IsFrame B) (hAB : A * B = B)
    (s : Address d (p ^ b)) : swapAt (p ^ b) A (swapAt (p ^ b) (A - B) s) = swapAt (p ^ b) B s := by
  have ha := frame_admissible hp hpb b hA
  have hb := frame_admissible hp hpb b hB
  have hm : reduce (p ^ b) A * reduce (p ^ b) B = reduce (p ^ b) B := by
    rw [← Swap.Modular.reduce_mul _ ha hb, hAB]
  simp only [swapAt]
  rw [exchange_exchange, reduce_sub _ ha hb, Matrix.mul_sub, hm, reduce_idem hp hpb b hA]
  congr 1
  rw [two_smul]
  abel

end Prime

/-! ### Edge programs -/

/-- An edge matrix: the difference of nested frames. -/
structure EdgeMat (U : Mat d) : Prop where
  idem : U * U = U
  bound : ∀ i j, (U i j).num.natAbs ≤ 10 ^ 10000 ∧ (U i j).den ≤ 10 ^ 10000

theorem edgeMat_sub {A B : Mat d} (hA : IsFrame A) (hB : IsFrame B) (hAB : A * B = A)
    (hBA : B * A = A) : EdgeMat (B - A) where
  idem := Exchange.sub_idempotent A B hA.idem hB.idem hAB hBA
  bound i j := by
    have h : Height.ht ((B - A) i j) ≤ 10 ^ 10000 := by
      rw [Matrix.sub_apply]
      refine (Height.ht_sub _ _).trans ?_
      calc 2 * Height.ht (B i j) * Height.ht (A i j) ≤ 2 * 10 ^ 4000 * 10 ^ 4000 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hB.bound i j)) (hA.bound i j)
        _ = 2 * 10 ^ 8000 := by rw [Nat.mul_assoc, ← pow_add]
        _ ≤ 10 * 10 ^ 8000 := Nat.mul_le_mul_right _ (by norm_num)
        _ = 10 ^ 8001 := (pow_succ' 10 8000).symm
        _ ≤ 10 ^ 10000 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact ⟨(Height.num_le_ht _).trans h, (Height.den_le_ht _).trans h⟩

/-- The stream map of an exchange program is precomposition with its partial swap. -/
theorem edgeAction_program {p : ℕ} (hp : p.Prime) (hpb : coefficientBound < p) (b : ℕ)
    {U : Mat d} (hU : EdgeMat U) (hd1 : 1 ≤ d) (hd : d ≤ 529) (f : Arrays d (p ^ b)) :
    edgeAction d (p ^ b) (Exchange.program U) f = fun a => f (swapAt (p ^ b) U a) := by
  have hrun : AffineFieldProgram.run (specialize (p ^ b) (Exchange.program U)) =
      Exchange.exchange (reduce (p ^ b) U) := funext fun s =>
    Exchange.specialize_run_of_bound U hU.idem (by simpa using hd1) (by simpa using hd) hU.bound
      hp hpb b s
  have hadm : Admissible (p ^ b) U := fun i j => by
    apply Nat.Coprime.pow_right
    have hden : (U i j).den < p :=
      lt_of_le_of_lt ((hU.bound i j).2.trans (by
        calc (10 : ℕ) ^ 10000 ≤ 16 ^ 10000 := Nat.pow_le_pow_left (by norm_num) _
          _ = 2 ^ 40000 := by rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
          _ ≤ coefficientBound := Exchange.le_coefficientBound
              (le_trans (by norm_num : (40000 : ℕ) ≤ 2 ^ 16)
                (Nat.pow_le_pow_right (by norm_num) (by norm_num))))) hpb
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (Nat.not_dvd_of_pos_of_lt (U i j).den_pos hden))
  have hinv : Function.Involutive (Exchange.exchange (reduce (p ^ b) U)) :=
    exchange_involutive (by rw [← Swap.Modular.reduce_mul _ hadm hadm, hU.idem])
  funext a
  simp only [edgeAction, hrun, swapAt]
  congr 1
  have := Function.leftInverse_invFun hinv.injective (Exchange.exchange (reduce (p ^ b) U) a)
  rwa [hinv a] at this

/-! ### Framed steps -/

/-- A framed step on wires `ι`. -/
inductive FStep (ι : Type) (d : ℕ) where
  | up (i : ι) (A B : Mat d)
  | down (i : ι) (A B : Mat d)
  | gate (g : Circuit.Gate ι (ZMod 2)) (F : Mat d)
  | reset (i : ι)
  | relabel (i : ι) (F : Mat d)

variable {ι : Type} [DecidableEq ι]

namespace FStep

/-- The physical steps. -/
def phys : FStep ι d → List (Step ι (FieldProgram d))
  | .up i A B => [.edge i (Exchange.program (B - A))]
  | .down i A B => [.edge i (Exchange.program (A - B))]
  | .gate g _ => [.gate g]
  | .reset i => [.reset i]
  | .relabel _ _ => []

/-- The frames after the step. -/
def frames : FStep ι d → (ι → Mat d) → (ι → Mat d)
  | .up i _ B, fr => Function.update fr i B
  | .down i _ B, fr => Function.update fr i B
  | .gate _ _, fr => fr
  | .reset _, fr => fr
  | .relabel i F, fr => Function.update fr i F

/-- The wires known to be zero after the step. -/
def zeros : FStep ι d → (ι → Prop) → (ι → Prop)
  | .gate g _, z => Function.update z g.target False
  | .reset i, z => Function.update z i True
  | _, z => z

/-- What the step needs of the current frames and zeros. -/
def Ok : FStep ι d → (ι → Mat d) → (ι → Prop) → Prop
  | .up i A B, fr, _ => fr i = A ∧ IsFrame B ∧ A * B = A ∧ B * A = A
  | .down i A B, fr, _ => fr i = A ∧ IsFrame B ∧ A * B = B ∧ B * A = B
  | .gate g F, fr, _ => (∀ w ∈ FramedCircuit.touched g, fr w = F) ∧
      ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src
  | .reset _, _, _ => True
  | .relabel i F, _, z => z i ∧ IsFrame F

/-- The step on logical streams. -/
def logic {E : Type} [AddCommGroup E] [Module (ZMod 2) E] : FStep ι d → (ι → E) → (ι → E)
  | .gate g _, x => FramedCircuit.moduleGate g x
  | .reset i, x => Function.update x i 0
  | _, x => x

end FStep

/-- The final frames of a list. -/
def finalFrames : List (FStep ι d) → (ι → Mat d) → (ι → Mat d)
  | [], fr => fr
  | s :: rest, fr => finalFrames rest (s.frames fr)

/-- The final zeros of a list. -/
def finalZeros : List (FStep ι d) → (ι → Prop) → (ι → Prop)
  | [], z => z
  | s :: rest, z => finalZeros rest (s.zeros z)

/-- Every step is valid in the frames and zeros left by the steps before it. -/
def Valid : List (FStep ι d) → (ι → Mat d) → (ι → Prop) → Prop
  | [], _, _ => True
  | s :: rest, fr, z => s.Ok fr z ∧ Valid rest (s.frames fr) (s.zeros z)

/-- The logical run. -/
def logicRun {E : Type} [AddCommGroup E] [Module (ZMod 2) E] :
    List (FStep ι d) → (ι → E) → (ι → E)
  | [], x => x
  | s :: rest, x => logicRun rest (s.logic x)

/-- The physical step list. -/
def physOf (L : List (FStep ι d)) : List (Step ι (FieldProgram d)) := L.flatMap FStep.phys

/-- Streams encode logical streams in frames. -/
def Encoded (q : ℕ) (fr : ι → Mat d) (stored ℓ : ι → Arrays d q) : Prop :=
  ∀ w a, stored w a = ℓ w (swapAt q (fr w) a)

theorem Step.run_append {P E : Type} [AddCommGroup E] [Module (ZMod 2) E] (edge : P → E → E)
    (s t : List (Step ι P)) (x : ι → E) : Step.run edge (s ++ t) x = Step.run edge t (Step.run edge s x) := by
  induction s generalizing x with
  | nil => rfl
  | cons st rest ih => exact ih _

section Run
variable {p : ℕ} (hp : p.Prime) (hpb : coefficientBound < p) (b : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ 529)
include hp hpb hd1 hd

/-- One framed step keeps the encoding. -/
theorem step_encoded (s : FStep ι d) (fr : ι → Mat d) (z : ι → Prop)
    (hfr : ∀ w, IsFrame (fr w)) (hok : s.Ok fr z) (stored ℓ : ι → Arrays d (p ^ b))
    (henc : Encoded (p ^ b) fr stored ℓ) (hz : ∀ w, z w → ℓ w = 0) :
    Encoded (p ^ b) (s.frames fr) (Step.run (edgeAction d (p ^ b)) s.phys stored) (s.logic ℓ) ∧
      (∀ w, s.zeros z w → s.logic ℓ w = 0) ∧ ∀ w, IsFrame (s.frames fr w) := by
  cases s with
  | up i A B =>
    obtain ⟨hi, hB, hAB, hBA⟩ := hok
    have hA : IsFrame A := hi ▸ hfr i
    refine ⟨fun w a => ?_, hz, fun w => ?_⟩
    · simp only [FStep.phys, FStep.frames, FStep.logic, Step.run, Step.execute]
      by_cases hw : w = i
      · subst hw
        rw [Function.update_self, Function.update_self,
          edgeAction_program hp hpb b (edgeMat_sub hA hB hAB hBA) hd1 hd]
        dsimp only
        rw [henc, hi, swapAt_up hp hpb b hA hB hAB]
      · rw [Function.update_of_ne hw, Function.update_of_ne hw, henc]
    · by_cases hw : w = i
      · subst hw; rw [FStep.frames, Function.update_self]; exact hB
      · rw [FStep.frames, Function.update_of_ne hw]; exact hfr w
  | down i A B =>
    obtain ⟨hi, hB, hAB, hBA⟩ := hok
    have hA : IsFrame A := hi ▸ hfr i
    refine ⟨fun w a => ?_, hz, fun w => ?_⟩
    · simp only [FStep.phys, FStep.frames, FStep.logic, Step.run, Step.execute]
      by_cases hw : w = i
      · subst hw
        rw [Function.update_self, Function.update_self,
          edgeAction_program hp hpb b (edgeMat_sub hB hA hBA hAB) hd1 hd]
        dsimp only
        rw [henc, hi, swapAt_down hp hpb b hA hB hAB]
      · rw [Function.update_of_ne hw, Function.update_of_ne hw, henc]
    · by_cases hw : w = i
      · subst hw; rw [FStep.frames, Function.update_self]; exact hB
      · rw [FStep.frames, Function.update_of_ne hw]; exact hfr w
  | gate g F =>
    obtain ⟨htouch, dst, src, hne, rfl⟩ := hok
    refine ⟨fun w a => ?_, fun w hw => ?_, hfr⟩
    · simp only [FStep.phys, FStep.frames, FStep.logic, Step.run, Step.execute]
      have hstored : stored = fun w a => ℓ w (swapAt (p ^ b) (fr w) a) := funext fun w =>
        funext fun a => henc w a
      have htd : fr dst = F := htouch dst (by simp [FramedCircuit.touched, ReversibleFanout.add])
      have hts : fr src = F := htouch src (by simp [FramedCircuit.touched, ReversibleFanout.add])
      rw [hstored]
      simp only [FramedCircuit.moduleGate, ReversibleFanout.add, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, one_smul]
      by_cases hw : w = dst
      · subst hw
        simp only [Function.update_self, Pi.add_apply]
        rw [htd, hts]
      · simp only [Function.update_of_ne hw]
    · simp only [FStep.zeros] at hw
      by_cases hwd : w = (ReversibleFanout.add dst src).target
      · rw [hwd, Function.update_self] at hw; exact hw.elim
      · rw [Function.update_of_ne hwd] at hw
        simp only [FStep.logic, FramedCircuit.moduleGate]
        rw [Function.update_of_ne hwd]
        exact hz w hw
  | reset i =>
    refine ⟨fun w a => ?_, fun w hw => ?_, hfr⟩
    · simp only [FStep.phys, FStep.frames, FStep.logic, Step.run, Step.execute]
      by_cases hw : w = i
      · subst hw; simp
      · rw [Function.update_of_ne hw, Function.update_of_ne hw, henc]
    · simp only [FStep.zeros] at hw
      simp only [FStep.logic]
      by_cases hwi : w = i
      · subst hwi; rw [Function.update_self]
      · rw [Function.update_of_ne hwi] at hw ⊢; exact hz w hw
  | relabel i F =>
    obtain ⟨hzi, hF⟩ := hok
    refine ⟨fun w a => ?_, hz, fun w => ?_⟩
    · simp only [FStep.phys, FStep.frames, FStep.logic, Step.run]
      by_cases hw : w = i
      · subst hw
        rw [Function.update_self, henc, hz w hzi]
        rfl
      · rw [Function.update_of_ne hw, henc]
    · by_cases hw : w = i
      · subst hw; rw [FStep.frames, Function.update_self]; exact hF
      · rw [FStep.frames, Function.update_of_ne hw]; exact hfr w

/-- **The framed run.** On streams encoding logical streams in the initial frames, with zero
logical streams on the initially zero wires, the physical run encodes the logical run in the
final frames. -/
theorem run_phys : ∀ (L : List (FStep ι d)) (fr : ι → Mat d) (z : ι → Prop),
    (∀ w, IsFrame (fr w)) → Valid L fr z → ∀ (stored ℓ : ι → Arrays d (p ^ b)),
    Encoded (p ^ b) fr stored ℓ → (∀ w, z w → ℓ w = 0) →
      Encoded (p ^ b) (finalFrames L fr) (Step.run (edgeAction d (p ^ b)) (physOf L) stored)
        (logicRun L ℓ)
  | [], _, _, _, _, _, _, henc, _ => henc
  | s :: rest, fr, z, hfr, hv, stored, ℓ, henc, hz => by
    obtain ⟨h1, h2, h3⟩ := step_encoded hp hpb b hd1 hd s fr z hfr hv.1 stored ℓ henc hz
    have := run_phys rest (s.frames fr) (s.zeros z) h3 hv.2 _ _ h1 h2
    rwa [physOf, List.flatMap_cons, Step.run_append]

end Run

/-! ### Interchange counts -/

/-- The interchanges of a framed list: the ranks of its edge matrices. -/
def edgeRanks : List (FStep ι d) → ℕ
  | [] => 0
  | .up _ A B :: rest => (B - A).rank + edgeRanks rest
  | .down _ A B :: rest => (A - B).rank + edgeRanks rest
  | _ :: rest => edgeRanks rest

omit [DecidableEq ι] in
theorem calls_physOf (L : List (FStep ι d)) : calls (physOf L) = edgeRanks L := by
  induction L with
  | nil => rfl
  | cons s rest ih =>
    cases s <;>
      simp [physOf, calls, Step.programs, edgeRanks, FStep.phys, Exchange.program_interchanges]
        at ih ⊢ <;>
      exact ih

end

end IntegerMultBounds.MathlibTM2.M8.Global
