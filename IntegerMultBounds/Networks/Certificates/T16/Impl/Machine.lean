module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Word
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-! **Machine primitives.** The layer machine acts on a 73-bit array by odd kernels (child calls),
translations, slot XORs `x_j ← x_j + x_i`, slot phases `i^{c x_i}` and unit scalars `i^c`. A
primitive is *ready* when it is a kernel, a permutation, a diagonal phase with a `Z/4`-quadratic
exponent or a fourth-root scalar. Every ready primitive is a word of machine primitives with the
same operator and the same number of child calls: permutations are products of slot XORs (a
transvection decomposition over `ZMod 2`), and the cross terms `2 x_i x_j` of a quadratic phase are
slot phases conjugated by a slot XOR, since `x_i + x_j - (x_i ⊕ x_j) = 2 x_i x_j`. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Matrix

/-! ### Slot XORs -/

/-- `x_j ← x_j + x_i` for `i ≠ j`, the identity for `i = j`. -/
def xorMap (i j : Fin 73) : Addr →ₗ[ZMod 2] Addr where
  toFun x := x + (if i = j then 0 else x i) • Pi.single j 1
  map_add' x y := by
    split_ifs
    · simp
    · simp only [Pi.add_apply, add_smul]; abel
  map_smul' c x := by
    split_ifs
    · simp
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]

theorem xorMap_apply (i j : Fin 73) (x : Addr) (k : Fin 73) :
    xorMap i j x k = x k + if i ≠ j ∧ k = j then x i else 0 := by
  change x k + ((if i = j then 0 else x i) • Pi.single j (1 : ZMod 2)) k = _
  by_cases hij : i = j
  · simp [hij]
  · by_cases hk : k = j
    · subst hk; simp [hij]
    · simp [hij, hk, Pi.single_apply]

theorem xorMap_involutive (i j : Fin 73) : Function.Involutive (xorMap i j) := by
  intro x
  funext k
  rw [xorMap_apply, xorMap_apply, xorMap_apply]
  by_cases h : i ≠ j ∧ k = j
  · obtain ⟨hij, rfl⟩ := h
    simp only [ne_eq, hij, not_false_eq_true, and_true, and_false, ↓reduceIte, add_zero]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · simp [h]

/-- The slot XOR as a linear equivalence. -/
noncomputable def xorEquiv (i j : Fin 73) : Addr ≃ₗ[ZMod 2] Addr :=
  LinearEquiv.ofInvolutive (xorMap i j) (xorMap_involutive i j)

theorem xorEquiv_symm_apply (i j : Fin 73) (x : Addr) : (xorEquiv i j).symm x = xorMap i j x := rfl

/-! ### Machine primitives -/

/-- One machine primitive on a 73-bit array. -/
inductive MPrim where
  | factor (q : ZMod 4) (v : Addr)
  | trans (v : Addr)
  | xor (i j : Fin 73)
  | phase (i : Fin 73) (c : ZMod 4)
  | unit (c : ZMod 4)

/-- The operator of a machine primitive. -/
noncomputable def MPrim.lin : MPrim → Module.End ℂ (Arrays 73)
  | .factor q v => BinaryWalsh.kernel q v
  | .trans v => BinaryWalsh.kernel 2 v
  | .xor i j => permOp (xorEquiv i j)
  | .phase i c => (phaseDiagonal fun x : Addr => c * bitLift (x i)).toLinearMap
  | .unit c => BinaryPhase.phase c • LinearMap.id

/-- Whether a machine primitive is a child call. -/
def MPrim.isChild : MPrim → Bool
  | .factor q _ => q.val % 2 == 1
  | _ => false

/-- The operator of a machine word, applied head first. -/
noncomputable def mwordLin : List MPrim → Module.End ℂ (Arrays 73)
  | [] => 1
  | p :: ps => mwordLin ps * p.lin

theorem mwordLin_append (ps qs : List MPrim) : mwordLin (ps ++ qs) = mwordLin qs * mwordLin ps := by
  induction ps with
  | nil => simp [mwordLin]
  | cons p ps ih => rw [List.cons_append, mwordLin, ih, mwordLin, mul_assoc]

/-- The child calls of a machine word. -/
def mchildCount (ps : List MPrim) : ℕ := (ps.filter MPrim.isChild).length

theorem mchildCount_append (ps qs : List MPrim) :
    mchildCount (ps ++ qs) = mchildCount ps + mchildCount qs := by
  simp [mchildCount, List.filter_append]

/-- A child-free machine word with operator `L`. -/
def Realizable (L : Module.End ℂ (Arrays 73)) : Prop :=
  ∃ ms : List MPrim, mchildCount ms = 0 ∧ mwordLin ms = L

theorem Realizable.one : Realizable 1 := ⟨[], rfl, rfl⟩

theorem Realizable.mul {A B : Module.End ℂ (Arrays 73)} (hA : Realizable A) (hB : Realizable B) :
    Realizable (B * A) := by
  obtain ⟨ma, ha, rfl⟩ := hA
  obtain ⟨mb, hb, rfl⟩ := hB
  exact ⟨ma ++ mb, by rw [mchildCount_append, ha, hb], mwordLin_append _ _⟩

theorem Realizable.single {p : MPrim} (hp : p.isChild = false) : Realizable p.lin :=
  ⟨[p], by simp [mchildCount, hp], by simp [mwordLin]⟩

/-! ### Permutations -/

/-- Pull back an array along a matrix. -/
def pullOp (M : Matrix (Fin 73) (Fin 73) (ZMod 2)) : Module.End ℂ (Arrays 73) where
  toFun f x := f (M.mulVec x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullOp_mul (A B : Matrix (Fin 73) (Fin 73) (ZMod 2)) : pullOp (A * B) = pullOp B * pullOp A := by
  apply LinearMap.ext
  intro f
  funext x
  change f ((A * B).mulVec x) = f (A.mulVec (B.mulVec x))
  rw [Matrix.mulVec_mulVec]

theorem pullOp_one : pullOp 1 = 1 := by
  apply LinearMap.ext
  intro f
  funext x
  change f ((1 : Matrix (Fin 73) (Fin 73) (ZMod 2)).mulVec x) = f x
  rw [Matrix.one_mulVec]

theorem transvection_mulVec (i j : Fin 73) (hij : i ≠ j) (x : Addr) :
    (transvection i j (1 : ZMod 2)).mulVec x = xorMap j i x := by
  funext k
  rw [xorMap_apply, transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  refine congrArg (x k + ·) ?_
  by_cases hk : k = i
  · subst hk
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Ne.symm hij]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hk, Ne.symm hk]

theorem realizable_pullOp_transvection (t : TransvectionStruct (Fin 73) (ZMod 2)) :
    Realizable (pullOp t.toMatrix) := by
  obtain ⟨i, j, hij, c⟩ := t
  obtain rfl | rfl : c = 0 ∨ c = 1 := by revert c; decide
  · change Realizable (pullOp (transvection i j 0))
    rw [transvection_zero, pullOp_one]
    exact Realizable.one
  · refine ⟨[.xor j i], rfl, ?_⟩
    apply LinearMap.ext
    intro f
    funext x
    change f ((xorEquiv j i).symm x) = f ((transvection i j (1 : ZMod 2)).mulVec x)
    rw [xorEquiv_symm_apply, transvection_mulVec i j hij]

theorem realizable_pullOp {M : Matrix (Fin 73) (Fin 73) (ZMod 2)} (hM : M.det ≠ 0) :
    Realizable (pullOp M) := by
  refine diagonal_transvection_induction_of_det_ne_zero (fun N => Realizable (pullOp N)) M hM
    (fun D hD => ?_) realizable_pullOp_transvection (fun A B _ _ hA hB => ?_)
  · have h1 : diagonal D = 1 := by
      rw [← diagonal_one]
      congr 1
      funext k
      have hk : D k ≠ 0 := by
        intro h0
        apply hD
        rw [det_diagonal]
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      generalize D k = d at hk
      fin_cases d
      · exact absurd rfl hk
      · rfl
    rw [h1, pullOp_one]
    exact Realizable.one
  · rw [pullOp_mul]
    exact hA.mul hB

/-- **Permutations are slot XOR words.** -/
theorem realizable_permOp (G : Addr ≃ₗ[ZMod 2] Addr) : Realizable (permOp G) := by
  have hdet : (LinearMap.toMatrix' G.symm.toLinearMap).det ≠ 0 := by
    intro h
    have e : LinearMap.toMatrix' G.symm.toLinearMap * LinearMap.toMatrix' G.toLinearMap = 1 := by
      rw [← LinearMap.toMatrix'_comp]
      simp
    have := congrArg Matrix.det e
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  have e : permOp G = pullOp (LinearMap.toMatrix' G.symm.toLinearMap) := by
    apply LinearMap.ext
    intro f
    funext x
    change f (G.symm x) = f ((LinearMap.toMatrix' G.symm.toLinearMap).mulVec x)
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  rw [e]
  exact realizable_pullOp hdet

/-! ### Quadratic phases -/

/-- A diagonal phase whose operator is a child-free machine word. -/
def DiagRealizable (ψ : Addr → ZMod 4) : Prop := Realizable (phaseDiagonal ψ).toLinearMap

theorem phaseDiagonal_add (ψ₁ ψ₂ : Addr → ZMod 4) :
    (phaseDiagonal (ψ₁ + ψ₂)).toLinearMap =
      (phaseDiagonal ψ₂).toLinearMap * (phaseDiagonal ψ₁).toLinearMap := by
  apply LinearMap.ext
  intro f
  funext x
  change phase (ψ₁ x + ψ₂ x) * f x = phase (ψ₂ x) * (phase (ψ₁ x) * f x)
  rw [phase_add]
  ring

theorem DiagRealizable.add {ψ₁ ψ₂ : Addr → ZMod 4} (h₁ : DiagRealizable ψ₁)
    (h₂ : DiagRealizable ψ₂) : DiagRealizable (ψ₁ + ψ₂) := by
  unfold DiagRealizable
  rw [phaseDiagonal_add]
  exact h₁.mul h₂

theorem diagRealizable_zero : DiagRealizable 0 := by
  unfold DiagRealizable
  convert Realizable.one
  apply LinearMap.ext
  intro f
  funext x
  change phase 0 * f x = f x
  rw [phase_zero, one_mul]

theorem diagRealizable_sum {ι : Type*} (s : Finset ι) (ψ : ι → Addr → ZMod 4)
    (h : ∀ i ∈ s, DiagRealizable (ψ i)) : DiagRealizable (∑ i ∈ s, ψ i) :=
  Finset.sum_induction _ DiagRealizable (fun _ _ => DiagRealizable.add) diagRealizable_zero h

theorem diagRealizable_const (k : ZMod 4) : DiagRealizable fun _ => k := by
  refine ⟨[.unit k], rfl, ?_⟩
  apply LinearMap.ext
  intro f
  funext x
  rfl

theorem diagRealizable_slot (i : Fin 73) (c : ZMod 4) :
    DiagRealizable fun x => c * bitLift (x i) :=
  ⟨[.phase i c], rfl, by simp [mwordLin, MPrim.lin]⟩

theorem bitLift_xor (a b : ZMod 2) :
    bitLift a + bitLift b - bitLift (b + a) = 2 * (bitLift a * bitLift b) := by
  revert a b; decide

theorem bitLift_sq (a : ZMod 2) : bitLift a * bitLift a = bitLift a := by
  revert a; decide

/-- The cross term `2 d x_i x_j`: two slot phases and a slot phase conjugated by a slot XOR. -/
theorem diagRealizable_cross (i j : Fin 73) (d : ZMod 4) :
    DiagRealizable fun x => 2 * d * (bitLift (x i) * bitLift (x j)) := by
  by_cases hij : i = j
  · subst hij
    convert diagRealizable_slot i (2 * d) using 2 with x
    rw [mul_assoc, bitLift_sq, mul_assoc]
  refine ⟨[.phase i d, .phase j d, .xor i j, .phase j (-d), .xor i j], rfl, ?_⟩
  apply LinearMap.ext
  intro f
  funext x
  have hxi : xorMap i j x i = x i := by
    rw [xorMap_apply]; simp
  have hxj : xorMap i j x j = x j + x i := by
    rw [xorMap_apply]; simp [hij]
  have hxx : xorMap i j (xorMap i j x) = x := xorMap_involutive i j x
  change phase (-d * bitLift ((xorMap i j x) j)) *
      (phase (d * bitLift ((xorMap i j (xorMap i j x)) j)) *
        (phase (d * bitLift ((xorMap i j (xorMap i j x)) i)) * f (xorMap i j (xorMap i j x)))) =
    phase (2 * d * (bitLift (x i) * bitLift (x j))) * f x
  rw [hxx, hxj, ← mul_assoc, ← mul_assoc, ← phase_add, ← phase_add]
  refine congrArg (fun q => phase q * f x) ?_
  rw [show 2 * d * (bitLift (x i) * bitLift (x j)) =
    d * (bitLift (x i) + bitLift (x j) - bitLift (x j + x i)) by rw [bitLift_xor]; ring]
  ring

/-- **Quadratic phases are slot phase and slot XOR words.** -/
theorem diagRealizable_of_quadratic {φ : Addr → ZMod 4} (h : Quadratic φ) : DiagRealizable φ := by
  obtain ⟨k, c, d, hφ⟩ := h
  have e : φ = ((fun _ => k) + ∑ i, fun x => c i * bitLift (x i)) +
      ∑ i, ∑ j, fun x => 2 * d i j * (bitLift (x i) * bitLift (x j)) := by
    funext x
    rw [hφ]
    simp [Finset.sum_apply]
  rw [e]
  refine ((diagRealizable_const k).add (diagRealizable_sum _ _ fun i _ =>
    diagRealizable_slot i (c i))).add (diagRealizable_sum _ _ fun i _ =>
      diagRealizable_sum _ _ fun j _ => diagRealizable_cross i j (d i j))

/-! ### Ready primitives -/

theorem kernel_zero_eq (v : Addr) : BinaryWalsh.kernel 0 v = 1 := by
  apply LinearMap.ext
  intro f
  funext x
  rw [BinaryWalsh.kernel_apply, phase_zero]
  simp

/-- **Ready primitives are machine words** with the same operator and child calls. -/
theorem Prim.Ready.lower {p : Prim} (h : p.Ready) :
    ∃ ms : List MPrim, mwordLin ms = p.lin ∧ mchildCount ms = childCount [p] := by
  cases p with
  | kernel q v =>
    obtain rfl | rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by clear h; revert q; decide
    · exact ⟨[], (kernel_zero_eq v).symm, rfl⟩
    · exact ⟨[.factor 1 v], by simp [mwordLin, MPrim.lin, Prim.lin], rfl⟩
    · exact ⟨[.trans v], by simp [mwordLin, MPrim.lin, Prim.lin], rfl⟩
    · exact ⟨[.factor 3 v], by simp [mwordLin, MPrim.lin, Prim.lin], rfl⟩
  | perm G =>
    obtain ⟨ms, hc, hl⟩ := realizable_permOp G
    exact ⟨ms, hl, hc⟩
  | diag φ =>
    obtain ⟨ms, hc, hl⟩ := diagRealizable_of_quadratic (show Quadratic φ from h)
    exact ⟨ms, hl, hc⟩
  | scale c =>
    obtain ⟨j, rfl⟩ := (show ∃ j : ZMod 4, c = phase j from h)
    exact ⟨[.unit j], by simp [mwordLin, MPrim.lin, Prim.lin], rfl⟩

open Classical in
/-- The machine word of a primitive (empty unless it is ready). -/
noncomputable def lowerPrim (p : Prim) : List MPrim :=
  if h : p.Ready then Classical.choose h.lower else []

theorem lowerPrim_spec {p : Prim} (h : p.Ready) :
    mwordLin (lowerPrim p) = p.lin ∧ mchildCount (lowerPrim p) = childCount [p] := by
  classical
  simp only [lowerPrim, h, ↓reduceDIte]
  exact Classical.choose_spec h.lower

/-! ### Machine programs -/

/-- One machine instruction: a rational gate or a machine primitive on one wire. -/
inductive MInstr (ι : Type) where
  | gate (g : Circuit.Gate ι ℚ)
  | prim (w : ι) (p : MPrim)

variable {ι : Type} [DecidableEq ι]
variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

noncomputable def MInstr.run : MInstr ι → (ι → S) → (ι → S)
  | .gate g, x => FramedCircuit.moduleGate g x
  | .prim w p, x => Function.update x w (ρ p.lin (x w))

/-- Run a machine program, head first. -/
noncomputable def runM : List (MInstr ι) → (ι → S) → (ι → S)
  | [], x => x
  | i :: is, x => runM is (i.run ρ x)

theorem runM_append (p q : List (MInstr ι)) (x : ι → S) :
    runM ρ (p ++ q) x = runM ρ q (runM ρ p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons i p ih => exact ih _

theorem runM_prims (w : ι) (ps : List MPrim) (x : ι → S) :
    runM ρ (ps.map (MInstr.prim w)) x = Function.update x w (ρ (mwordLin ps) (x w)) := by
  induction ps generalizing x with
  | nil =>
    change x = Function.update x w (ρ 1 (x w))
    rw [map_one, Module.End.one_apply, Function.update_eq_self]
  | cons p ps ih =>
    simp only [List.map_cons, runM, MInstr.run]
    rw [ih, Function.update_self, Function.update_idem, mwordLin, map_mul, Module.End.mul_apply]

/-- The child calls of a machine program. -/
def MInstr.isChild : MInstr ι → Bool
  | .gate _ => false
  | .prim _ p => p.isChild

def mprogramChildren (p : List (MInstr ι)) : ℕ := (p.filter MInstr.isChild).length

omit [DecidableEq ι] in
theorem mprogramChildren_append (p q : List (MInstr ι)) :
    mprogramChildren (p ++ q) = mprogramChildren p + mprogramChildren q := by
  simp [mprogramChildren, List.filter_append]

omit [DecidableEq ι] in
theorem mprogramChildren_prims (w : ι) (ps : List MPrim) :
    mprogramChildren (ps.map (MInstr.prim w)) = mchildCount ps := by
  simp only [mprogramChildren, mchildCount, ← List.countP_eq_length_filter, List.countP_map]
  rfl

/-- Whether an instruction's primitive is ready. -/
def TInstr.Ready : TInstr ι → Prop
  | .gate _ => True
  | .prim _ p => p.Ready

/-- The machine instructions of an instruction. -/
noncomputable def lowerInstr : TInstr ι → List (MInstr ι)
  | .gate g => [.gate g]
  | .prim w p => (lowerPrim p).map (MInstr.prim w)

/-- The machine program of a program. -/
noncomputable def lowerProgram (prog : List (TInstr ι)) : List (MInstr ι) := prog.flatMap lowerInstr

/-- **Lowering to the machine.** A program of ready primitives and its machine program act
alike, for every representation, and make the same child calls. -/
theorem lowerProgram_spec (prog : List (TInstr ι)) (h : ∀ i ∈ prog, i.Ready) :
    (∀ y : ι → S, runM ρ (lowerProgram prog) y = runT ρ prog y) ∧
      mprogramChildren (lowerProgram prog) = programChildren prog := by
  induction prog with
  | nil => exact ⟨fun _ => rfl, rfl⟩
  | cons i prog ih =>
    obtain ⟨ihr, ihc⟩ := ih fun i' h' => h i' (List.mem_cons_of_mem _ h')
    have hi := h i List.mem_cons_self
    rw [lowerProgram, List.flatMap_cons, ← lowerProgram]
    cases i with
    | gate g =>
      refine ⟨fun y => ?_, ?_⟩
      · rw [runM_append]
        exact ihr _
      · rw [mprogramChildren_append, ihc, show programChildren (TInstr.gate g :: prog) =
          programChildren [TInstr.gate g] + programChildren prog from programChildren_append [TInstr.gate g] prog]
        rfl
    | prim w p =>
      obtain ⟨hl, hc⟩ := lowerPrim_spec (show p.Ready from hi)
      refine ⟨fun y => ?_, ?_⟩
      · rw [runM_append, lowerInstr, runM_prims, hl, ihr]
        rfl
      · rw [mprogramChildren_append, lowerInstr, mprogramChildren_prims, hc, ihc,
          show programChildren (TInstr.prim w p :: prog) =
            programChildren ([p].map (TInstr.prim w)) + programChildren prog from
              programChildren_append [TInstr.prim w p] prog, programChildren_prims]

end IntegerMultBounds.Networks.Certificates.T16.Impl
