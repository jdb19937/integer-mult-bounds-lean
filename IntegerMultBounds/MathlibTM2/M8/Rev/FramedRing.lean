module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeRun

/-!
# The framed node over any coordinate ring

`Global.run_phys` and `Global.node_run` work over the addresses `(ℤ/p^b)^m × (ℤ/p^b)^m`, with
every frame read through its reduction mod `p^b`. The argument uses only that this reading is
multiplicative and additive on frames and keeps `0` and `1`. Here it is restated for any
commutative ring `R` and any such reading `ρ` of the rational frames (`Interp`): the physical
run of a framed list (`frun`, every frame change `D_U` acting as the partial swap of `ρ U`)
encodes the logical run (`frun_encoded`), and the PR97 node is the routed transpose on
arbitrary streams over `R` (`node_run_ring`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Rev

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Global

variable {d : ℕ} {R : Type} [CommRing R]

/-- A reading of the rational frames as matrices over `R`, multiplicative and additive on
frames. -/
structure Interp (d : ℕ) (R : Type) [CommRing R] where
  ρ : Mat d → Matrix (Fin d) (Fin d) R
  mul : ∀ {A B : Mat d}, IsFrame A → IsFrame B → ρ (A * B) = ρ A * ρ B
  sub : ∀ {A B : Mat d}, IsFrame A → IsFrame B → ρ (B - A) = ρ B - ρ A
  one : ρ 1 = 1
  zero : ρ 0 = 0

/-- An address pair over `R`. -/
abbrev Addr (d : ℕ) (R : Type) := (Fin d → R) × (Fin d → R)

/-- A stream: one bit per address pair. -/
abbrev Streams (d : ℕ) (R : Type) := Addr d R → ZMod 2

namespace Interp

variable (I : Interp d R)

/-- The partial swap of a frame. -/
def swap (U : Mat d) : Addr d R → Addr d R := Exchange.exchange (I.ρ U)

theorem idem {U : Mat d} (hU : IsFrame U) : I.ρ U * I.ρ U = I.ρ U := by
  rw [← I.mul hU hU, hU.idem]

theorem swap_involutive {U : Mat d} (hU : IsFrame U) : Function.Involutive (I.swap U) :=
  exchange_involutive (I.idem hU)

theorem swap_up {A B : Mat d} (hA : IsFrame A) (hB : IsFrame B) (hAB : A * B = A) (s : Addr d R) :
    I.swap A (I.swap (B - A) s) = I.swap B s := by
  have hm : I.ρ A * I.ρ B = I.ρ A := by rw [← I.mul hA hB, hAB]
  simp only [swap]
  rw [exchange_exchange, I.sub hA hB, Matrix.mul_sub, hm, I.idem hA, sub_self, smul_zero, sub_zero,
    add_sub_cancel]

theorem swap_down {A B : Mat d} (hA : IsFrame A) (hB : IsFrame B) (hAB : A * B = B) (s : Addr d R) :
    I.swap A (I.swap (A - B) s) = I.swap B s := by
  have hm : I.ρ A * I.ρ B = I.ρ B := by rw [← I.mul hA hB, hAB]
  simp only [swap]
  rw [exchange_exchange, I.sub hB hA, Matrix.mul_sub, hm, I.idem hA]
  congr 1
  rw [two_smul]
  abel

theorem swap_zero (a : Addr d R) : I.swap 0 a = a := by
  rw [swap, I.zero]; exact exchange_zero a

theorem swap_one (a : Addr d R) : I.swap 1 a = (a.2, a.1) := by
  rw [swap, I.one]; simp [Exchange.exchange]

end Interp

variable {ι : Type} [DecidableEq ι]

/-- The physical action of a framed step over `R`. -/
def fstep (I : Interp d R) : FStep ι d → (ι → Streams d R) → (ι → Streams d R)
  | .up i A B, x => Function.update x i (fun a => x i (I.swap (B - A) a))
  | .down i A B, x => Function.update x i (fun a => x i (I.swap (A - B) a))
  | .gate g _, x => FramedCircuit.moduleGate g x
  | .reset i, x => Function.update x i 0
  | .relabel _ _, x => x

/-- The physical run of a framed list over `R`. -/
def frun (I : Interp d R) : List (FStep ι d) → (ι → Streams d R) → (ι → Streams d R)
  | [], x => x
  | s :: rest, x => frun I rest (fstep I s x)

theorem frun_append (I : Interp d R) (L L' : List (FStep ι d)) (x : ι → Streams d R) :
    frun I (L ++ L') x = frun I L' (frun I L x) := by
  induction L generalizing x with
  | nil => rfl
  | cons s rest ih => exact ih _

/-- Streams encode logical streams in frames. -/
def REncoded (I : Interp d R) (fr : ι → Mat d) (stored ℓ : ι → Streams d R) : Prop :=
  ∀ w a, stored w a = ℓ w (I.swap (fr w) a)

/-- One framed step keeps the encoding. -/
theorem fstep_encoded (I : Interp d R) (s : FStep ι d) (fr : ι → Mat d) (z : ι → Prop)
    (hfr : ∀ w, IsFrame (fr w)) (hok : s.Ok fr z) (stored ℓ : ι → Streams d R)
    (henc : REncoded I fr stored ℓ) (hz : ∀ w, z w → ℓ w = 0) :
    REncoded I (s.frames fr) (fstep I s stored) (s.logic ℓ) ∧
      (∀ w, s.zeros z w → s.logic ℓ w = 0) ∧ ∀ w, IsFrame (s.frames fr w) := by
  cases s with
  | up i A B =>
    obtain ⟨hi, hB, hAB, -⟩ := hok
    have hA : IsFrame A := hi ▸ hfr i
    refine ⟨fun w a => ?_, hz, fun w => ?_⟩
    · simp only [fstep, FStep.frames, FStep.logic]
      by_cases hw : w = i
      · subst hw
        rw [Function.update_self, Function.update_self, henc, hi, I.swap_up hA hB hAB]
      · rw [Function.update_of_ne hw, Function.update_of_ne hw, henc]
    · by_cases hw : w = i
      · subst hw; rw [FStep.frames, Function.update_self]; exact hB
      · rw [FStep.frames, Function.update_of_ne hw]; exact hfr w
  | down i A B =>
    obtain ⟨hi, hB, hAB, -⟩ := hok
    have hA : IsFrame A := hi ▸ hfr i
    refine ⟨fun w a => ?_, hz, fun w => ?_⟩
    · simp only [fstep, FStep.frames, FStep.logic]
      by_cases hw : w = i
      · subst hw
        rw [Function.update_self, Function.update_self, henc, hi, I.swap_down hA hB hAB]
      · rw [Function.update_of_ne hw, Function.update_of_ne hw, henc]
    · by_cases hw : w = i
      · subst hw; rw [FStep.frames, Function.update_self]; exact hB
      · rw [FStep.frames, Function.update_of_ne hw]; exact hfr w
  | gate g F =>
    obtain ⟨htouch, dst, src, hne, rfl⟩ := hok
    refine ⟨fun w a => ?_, fun w hw => ?_, hfr⟩
    · simp only [fstep, FStep.frames, FStep.logic]
      have hstored : stored = fun w a => ℓ w (I.swap (fr w) a) := funext fun w =>
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
    · simp only [fstep, FStep.frames, FStep.logic]
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
    · simp only [fstep, FStep.frames, FStep.logic]
      by_cases hw : w = i
      · subst hw
        rw [Function.update_self, henc, hz w hzi]
        rfl
      · rw [Function.update_of_ne hw, henc]
    · by_cases hw : w = i
      · subst hw; rw [FStep.frames, Function.update_self]; exact hF
      · rw [FStep.frames, Function.update_of_ne hw]; exact hfr w

/-- **The framed run over `R`.** -/
theorem frun_encoded (I : Interp d R) : ∀ (L : List (FStep ι d)) (fr : ι → Mat d) (z : ι → Prop),
    (∀ w, IsFrame (fr w)) → Valid L fr z → ∀ (stored ℓ : ι → Streams d R),
    REncoded I fr stored ℓ → (∀ w, z w → ℓ w = 0) →
      REncoded I (finalFrames L fr) (frun I L stored) (logicRun L ℓ)
  | [], _, _, _, _, _, _, henc, _ => henc
  | s :: rest, fr, z, hfr, hv, stored, ℓ, henc, hz => by
    obtain ⟨h1, h2, h3⟩ := fstep_encoded I s fr z hfr hv.1 stored ℓ henc hz
    exact frun_encoded I rest (s.frames fr) (s.zeros z) h3 hv.2 _ _ h1 h2

/-! ### The PR97 node over `R` -/

open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical in
theorem swap_gauge (I : Interp 529 R) (S T : V) (a : Addr 529 R) :
    I.swap (uFrame S T) (I.swap (1 - uFrame S T) a) = I.swap 1 a := by
  have hU : IsFrame (uFrame S T) := lframe_lift1 T (lframe_lineOf S)
  simp only [Interp.swap]
  rw [exchange_exchange, I.sub hU (isFrame_one (d := 529)), I.one, Matrix.mul_sub, Matrix.mul_one,
    I.idem hU, sub_self, smul_zero, sub_zero, add_sub_cancel]

open Classical in
/-- **The PR97 node over any coordinate ring.** On arbitrary stored streams of the contract
roles and zero temporaries, every contract role ends with the stream of its route, address
fields exchanged. -/
theorem node_run_ring (I : Interp 529 R) (stored : Wire → Streams 529 R)
    (hz : ∀ t, stored (.inr t) = 0) (i : World) (a : Addr 529 R) :
    frun I framedNode stored (.inl i) a = stored (.inl (route i)) (a.2, a.1) := by
  set ℓ0 : Wire → Streams 529 R := fun w a => stored w (I.swap (gInit w) a)
  have henc : REncoded I gInit stored ℓ0 := fun w a => by
    simp only [ℓ0]
    rw [I.swap_involutive (isFrame_gInit w)]
  have hzero : ∀ w, tempZero w → ℓ0 w = 0 := by
    rintro w ⟨t, rfl⟩
    funext a
    simp only [ℓ0, hz t, Pi.zero_apply]
  have hrun := frun_encoded I framedNode gInit tempZero isFrame_gInit valid_node stored ℓ0 henc hzero
  have hlogic : logicRun framedNode ℓ0 = FramedCircuit.moduleRun (allGates.map FGate.gate) ℓ0 := by
    rw [framedNode, logicRun_append, sinks, logicRun_alignMoves, logicRun_autoSteps]
  have hpt : ∀ w (a' : Addr 529 R), logicRun framedNode ℓ0 w a' =
      Circuit.run (allGates.map FGate.gate) (fun w' => ℓ0 w' a') w := fun w a' => by
    rw [hlogic, FramedCircuit.moduleRun_pointwise]
  have hz' : ∀ (a' : Addr 529 R) (t : Temp), (fun w' => ℓ0 w' a') (.inr t) = 0 := by
    intro a' t
    simp only [ℓ0, hz t, Pi.zero_apply]
  rw [hrun (.inl i) a, hpt]
  rcases i with ⟨S, T⟩ | ⟨S, T⟩ | ⟨b', T, s⟩
  · rw [show (.inl (.inl (S, T)) : Wire) = wX S T from rfl, final_wX,
      (node_scalar _ (hz' _)).1 S T]
    simp only [ℓ0, wY, route]
    rw [show gInit (.inl (.inr (.inl (S, T)))) = 0 from rfl, I.swap_zero, I.swap_one]
  · rw [show (.inl (.inr (.inl (S, T))) : Wire) = wY S T from rfl, final_wY,
      (node_scalar _ (hz' _)).2.1 S T]
    simp only [ℓ0, wX, route]
    rw [show gInit (.inl (.inl (S, T))) = uFrame S T from rfl, swap_gauge, I.swap_one]
  · rw [show (.inl (.inr (.inr (b', T, s))) : Wire) = wSide b' T s from rfl, final_side,
      (node_scalar _ (hz' _)).2.2 b' T s]
    simp only [ℓ0, wSide, route]
    rw [show gInit (.inl (.inr (.inr (b', T, s)))) = 0 from rfl, I.swap_zero, I.swap_one]

end

end IntegerMultBounds.MathlibTM2.M8.Rev
