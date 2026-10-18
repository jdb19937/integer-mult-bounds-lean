module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.MachineFit

/-! **The T16 layer program.** The instructions of the layer machine: factors `(q, v)` with
`q = ±1` (child calls), half-integral rational gates, translations by vectors with a zero
coordinate, slot XORs `x_j ← x_j + x_i` (`i ≠ j`) and slot phases `i^{c x_i}`. Unit scalars are
slot phases around two translations (`i^c = i^{c x_0} · i^{c (1 - x_0)}`), and translations by
the all-ones vector are two translations. `layerProgram` is the fitted T16 machine program in
these instructions: it applies `C_all` to every family, for every representation, and makes
exactly `1,041,408` child calls. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams

/-- One instruction of the layer machine. -/
inductive KInstr (ι : Type) where
  | factor (w : ι) (g : ZMod 4 × Addr)
  | gate (g : Circuit.Gate ι ℚ)
  | trans (w : ι) (v : Addr)
  | xor (w : ι) (i j : Fin 73)
  | phase (w : ι) (i : Fin 73) (c : ZMod 4)

/-- The slot phase `i^{c x_i}`. -/
noncomputable def slotPhase (i : Fin 73) (c : ZMod 4) : Module.End ℂ (Arrays 73) :=
  (phaseDiagonal fun x : Addr => c * bitLift (x i)).toLinearMap

variable {ι : Type} [DecidableEq ι]
variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

/-- One instruction under a representation. -/
noncomputable def KInstr.run : KInstr ι → (ι → S) → (ι → S)
  | .factor w g, x => Function.update x w (ρ (BinaryWalsh.kernel g.1 g.2) (x w))
  | .gate g, x => FramedCircuit.moduleGate g x
  | .trans w v, x => Function.update x w (ρ (BinaryWalsh.kernel 2 v) (x w))
  | .xor w i j, x => Function.update x w (ρ (permOp (xorEquiv i j)) (x w))
  | .phase w i c, x => Function.update x w (ρ (slotPhase i c) (x w))

/-- Run a layer program, head first. -/
noncomputable def runK : List (KInstr ι) → (ι → S) → (ι → S)
  | [], x => x
  | i :: is, x => runK is (i.run ρ x)

theorem runK_append (p q : List (KInstr ι)) (x : ι → S) :
    runK ρ (p ++ q) x = runK ρ q (runK ρ p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons i p ih => exact ih _

/-- Whether an instruction is a child call. -/
def KInstr.isChild : KInstr ι → Bool
  | .factor _ _ => true
  | _ => false

/-- The child calls of a layer program. -/
def kChildren (p : List (KInstr ι)) : ℕ := (p.filter KInstr.isChild).length

omit [DecidableEq ι] in
theorem kChildren_append (p q : List (KInstr ι)) : kChildren (p ++ q) = kChildren p + kChildren q := by
  simp [kChildren, List.filter_append]

/-- The instructions the machine runs directly. -/
def KInstr.Fit : KInstr ι → Prop
  | .factor _ g => g.1 = 1 ∨ g.1 = -1
  | .gate g => HalfGate g
  | .trans _ v => ∃ x, v x = 0
  | .xor _ i j => i ≠ j
  | .phase _ _ _ => True

/-! ### Operator identities -/

theorem kernel_two_apply (v : Addr) (f : Arrays 73) (x : Addr) :
    BinaryWalsh.kernel 2 v f x = f (x + v) := by
  rw [BinaryWalsh.kernel_apply, Pauli.phase_two]
  ring

theorem kernel_two_mul (a b : Addr) :
    BinaryWalsh.kernel 2 b * BinaryWalsh.kernel 2 a = BinaryWalsh.kernel 2 (a + b) := by
  apply LinearMap.ext
  intro f
  funext x
  change BinaryWalsh.kernel 2 b (BinaryWalsh.kernel 2 a f) x = _
  rw [kernel_two_apply, kernel_two_apply, kernel_two_apply, add_assoc, add_comm b a]

theorem slotPhase_apply (i : Fin 73) (c : ZMod 4) (f : Arrays 73) (x : Addr) :
    slotPhase i c f x = phase (c * bitLift (x i)) * f x := rfl

/-- `i^c` as two slot phases around two translations. -/
theorem unit_eq (c : ZMod 4) :
    BinaryWalsh.kernel 2 (Pi.single 0 1) * slotPhase 0 c * BinaryWalsh.kernel 2 (Pi.single 0 1) *
      slotPhase 0 c = BinaryPhase.phase c • LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext x
  change BinaryWalsh.kernel 2 (Pi.single 0 1) (slotPhase 0 c
    (BinaryWalsh.kernel 2 (Pi.single 0 1) (slotPhase 0 c f))) x = phase c * f x
  have h2 : x + Pi.single 0 1 + Pi.single 0 1 = x := by
    funext t
    simp only [Pi.add_apply]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [kernel_two_apply, slotPhase_apply, kernel_two_apply, slotPhase_apply, h2, ← mul_assoc,
    ← phase_add, ← mul_add]
  have hb : ∀ b : ZMod 2, bitLift (b + 1) + bitLift b = 1 := by decide
  have hx : (x + Pi.single (0 : Fin 73) (1 : ZMod 2) : Addr) 0 = x 0 + 1 := by simp
  rw [hx, hb, mul_one]

theorem kernel_two_zero : BinaryWalsh.kernel 2 (0 : Addr) = 1 := by
  apply LinearMap.ext; intro f; funext x; rw [kernel_two_apply, add_zero]; rfl

theorem permOp_xor_self (i : Fin 73) : permOp (xorEquiv i i) = 1 := by
  apply LinearMap.ext; intro f; funext x
  change f (xorMap i i x) = f x
  congr 1
  funext t
  rw [xorMap_apply]
  simp

/-! ### The conversion -/

/-- The first basis vector. -/
def e0 : Addr := Pi.single 0 1

open Classical in
/-- A translation as translations by vectors with a zero coordinate. -/
noncomputable def transK (w : ι) (v : Addr) : List (KInstr ι) :=
  if v = 0 then [] else if ∃ x, v x = 0 then [.trans w v] else [.trans w e0, .trans w (v + e0)]

/-- The layer instructions of a machine instruction. -/
noncomputable def toK : MInstr ι → List (KInstr ι)
  | .gate g => [.gate g]
  | .prim w (.factor q v) =>
    if q = 1 ∨ q = 3 then [.factor w (q, v)] else if q = 2 then transK w v else []
  | .prim w (.trans v) => transK w v
  | .prim w (.xor i j) => if i = j then [] else [.xor w i j]
  | .prim w (.phase i c) => [.phase w i c]
  | .prim w (.unit c) => [.phase w 0 c, .trans w e0, .phase w 0 c, .trans w e0]

omit [Module ℚ S] in
theorem run_update_update (w : ι) (A B : Module.End ℂ (Arrays 73)) (x : ι → S) :
    Function.update (Function.update x w (ρ A (x w))) w
        (ρ B (Function.update x w (ρ A (x w)) w)) = Function.update x w (ρ (B * A) (x w)) := by
  rw [Function.update_self, Function.update_idem, map_mul, Module.End.mul_apply]

omit [Module ℚ S] in
theorem update_one (w : ι) (x : ι → S) : Function.update x w (ρ 1 (x w)) = x := by
  rw [map_one, Module.End.one_apply, Function.update_eq_self]

theorem runK_transK (w : ι) (v : Addr) (x : ι → S) :
    runK ρ (transK w v) x = Function.update x w (ρ (BinaryWalsh.kernel 2 v) (x w)) := by
  classical
  unfold transK
  split_ifs with h0 h1
  · subst h0; rw [kernel_two_zero, update_one]; rfl
  · rfl
  · change Function.update (Function.update x w (ρ (BinaryWalsh.kernel 2 e0) (x w))) w
      (ρ (BinaryWalsh.kernel 2 (v + e0)) (Function.update x w (ρ (BinaryWalsh.kernel 2 e0) (x w)) w)) = _
    rw [run_update_update, kernel_two_mul, add_comm e0, add_assoc, show e0 + e0 = 0 by
      funext t; simp only [Pi.add_apply, Pi.zero_apply]; exact CharTwo.add_self_eq_zero _, add_zero]

/-- **The conversion is exact.** -/
theorem runK_toK (i : MInstr ι) (x : ι → S) : runK ρ (toK i) x = i.run ρ x := by
  cases i with
  | gate g => rfl
  | prim w p =>
    cases p with
    | factor q v =>
      obtain rfl | rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by revert q; decide
      · simp only [toK, show ¬((0 : ZMod 4) = 1 ∨ (0 : ZMod 4) = 3) by decide,
          show ¬((0 : ZMod 4) = 2) by decide, ↓reduceIte]
        change x = Function.update x w (ρ (BinaryWalsh.kernel 0 v) (x w))
        rw [kernel_zero_eq, update_one]
      · rfl
      · simp only [toK, show ¬((2 : ZMod 4) = 1 ∨ (2 : ZMod 4) = 3) by decide, ↓reduceIte]
        exact runK_transK ρ w v x
      · rfl
    | trans v => exact runK_transK ρ w v x
    | xor i j =>
      simp only [toK]
      split_ifs with hij
      · subst hij
        change x = Function.update x w (ρ (permOp (xorEquiv i i)) (x w))
        rw [permOp_xor_self, update_one]
      · rfl
    | phase i c => rfl
    | unit c =>
      simp only [toK, runK, KInstr.run]
      rw [run_update_update, run_update_update, run_update_update, e0, unit_eq]
      rfl

omit [DecidableEq ι] in
theorem kChildren_transK (w : ι) (v : Addr) : kChildren (transK w v) = 0 := by
  classical
  unfold transK
  split_ifs <;> rfl

omit [DecidableEq ι] in
theorem kChildren_toK (i : MInstr ι) : kChildren (toK i) = mprogramChildren [i] := by
  cases i with
  | gate g => rfl
  | prim w p =>
    cases p with
    | factor q v =>
      obtain rfl | rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by revert q; decide
      · simp only [toK, show ¬((0 : ZMod 4) = 1 ∨ (0 : ZMod 4) = 3) by decide,
          show ¬((0 : ZMod 4) = 2) by decide, ↓reduceIte]; rfl
      · rfl
      · simp only [toK, show ¬((2 : ZMod 4) = 1 ∨ (2 : ZMod 4) = 3) by decide, ↓reduceIte]
        rw [kChildren_transK]; rfl
      · rfl
    | trans v => rw [toK, kChildren_transK]; rfl
    | xor i j => simp only [toK]; split_ifs <;> rfl
    | phase i c => rfl
    | unit c => rfl

omit [DecidableEq ι] in
theorem fit_transK (w : ι) (v : Addr) : ∀ i ∈ transK w v, i.Fit := by
  classical
  unfold transK
  split_ifs with h0 h1
  · simp
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; exact h1
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    push Not at h1
    rcases hi with rfl | rfl
    · exact ⟨1, by simp [e0]⟩
    · refine ⟨0, ?_⟩
      have h := h1 0
      simp only [Pi.add_apply, e0, Pi.single_eq_same]
      generalize v 0 = b at h ⊢
      revert b; decide

omit [DecidableEq ι] in
theorem fit_toK (i : MInstr ι) (hi : ∀ g, i = .gate g → HalfGate g) : ∀ k ∈ toK i, k.Fit := by
  cases i with
  | gate g => intro k hk; simp only [toK, List.mem_singleton] at hk; subst hk; exact hi g rfl
  | prim w p =>
    clear hi
    cases p with
    | factor q v =>
      obtain rfl | rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by revert q; decide
      · simp [toK, show ¬((0 : ZMod 4) = 1 ∨ (0 : ZMod 4) = 3) by decide,
          show ¬((0 : ZMod 4) = 2) by decide]
      · intro k hk; simp only [toK, List.mem_singleton, true_or, ↓reduceIte] at hk
        subst hk; exact Or.inl rfl
      · simp only [toK, show ¬((2 : ZMod 4) = 1 ∨ (2 : ZMod 4) = 3) by decide, ↓reduceIte]
        exact fit_transK w v
      · intro k hk; simp only [toK, List.mem_singleton, or_true, ↓reduceIte] at hk
        subst hk; exact Or.inr (show (3 : ZMod 4) = -1 by decide)
    | trans v => exact fit_transK w v
    | xor i j =>
      intro k hk
      simp only [toK] at hk
      split_ifs at hk with hij
      · simp at hk
      · simp only [List.mem_singleton] at hk; subst hk; exact hij
    | phase i c => intro k hk; simp only [toK, List.mem_singleton] at hk; subst hk; trivial
    | unit c =>
      intro k hk
      simp only [toK, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · trivial
      · exact ⟨1, by simp [e0]⟩
      · trivial
      · exact ⟨1, by simp [e0]⟩

/-! ### The layer program -/

/-- **The T16 node as a layer program.** -/
noncomputable def layerProgram : List (KInstr NodeUnit) := fittedProgram.flatMap toK

theorem runK_flatMap_toK (p : List (MInstr ι)) (x : ι → S) :
    runK ρ (p.flatMap toK) x = runM ρ p x := by
  induction p generalizing x with
  | nil => rfl
  | cons i p ih => rw [List.flatMap_cons, runK_append, runK_toK, ih]; rfl

theorem kChildren_flatMap_toK (p : List (MInstr ι)) :
    kChildren (p.flatMap toK) = mprogramChildren p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    rw [List.flatMap_cons, kChildren_append, kChildren_toK, ih,
      ← mprogramChildren_append [i] p]
    rfl

/-- **The layer program applies `C_all` to every family.** -/
theorem layerProgram_cAll [IsScalarTower ℚ ℂ S] (y : NodeUnit → S) {r a : ℕ} (hr : r < 16)
    (ha : a < 112) (i : Fin 8) :
    runK ρ layerProgram y (streamUnit r a i) = ρ cAll (y (streamUnit r a i)) := by
  rw [layerProgram, runK_flatMap_toK, fittedProgram_cAll ρ y hr ha i]

/-- **The layer program makes exactly `F = 1,041,408` child calls.** -/
theorem layerProgram_children : kChildren layerProgram = 1041408 := by
  rw [layerProgram, kChildren_flatMap_toK, fittedProgram_children]

/-- **Every instruction of the layer program runs on the machine.** -/
theorem layerProgram_fit : ∀ k ∈ layerProgram, k.Fit := by
  intro k hk
  rw [layerProgram, List.mem_flatMap] at hk
  obtain ⟨i, hi, hk⟩ := hk
  exact fit_toK i (fun g hg => fittedProgram_half g (hg ▸ hi)) k hk

end IntegerMultBounds.Networks.Certificates.T16.Impl
