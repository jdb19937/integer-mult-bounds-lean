module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreRun

/-!
# The stage-2 core on a caller's tape

The core's bank (`Assembly.bank`) is a function of the stream on its I/O role (`bankWith`). Placed
with that role shared with a caller's tape (`program`), the core transposes the bit array on the
caller's tape and restores its own bank, the core's bank with a blank I/O role (`privateBank`):
`runs`, from `CoreRun.core_run`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreShared

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open Stage2Width (tau2)
open RevMachine
open FamilyRoot (ext FamilySpec)
open Assembly (tW wOf nOf)

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

/-- The core's bank with the stream `src` on the I/O role. -/
def bankWith (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (w : ℕ) (u : Descriptor) (src : ℤ → Fin (prime+4)) : Tapes (tW capacity) prime :=
  raw (CommonBank.bank (NodePark.childRoles rev97m src) (Routines.hdr u) f p node scalar
    (Prepare.rest w 529) st) (tW capacity)

/-- The core's own bank: its bank at the view `v` with a blank I/O role. -/
def privateBank (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime) (w : ℕ)
    (v : Descriptor) : Tapes (tW capacity) prime :=
  bankWith capacity f p node (Place.memo v.width) st w v (fun _ => blank)

theorem io_lt : (NodeBank.io rev97m).val < tW capacity :=
  lt_of_lt_of_le (NodeBank.io rev97m).isLt
    ((Nat.le_add_right _ _).trans ((Assembly.count_le capacity).trans (Assembly.tF_le capacity)))

/-- The I/O role among the core's tapes. -/
def ioSlot : Fin (tW capacity) := ⟨(NodeBank.io rev97m).val, io_lt capacity⟩

omit [M8.Machine.Net] in
theorem io_lt_count : (NodeBank.io rev97m).val < CommonBank.count (NodeBank.tapes rev97m) :=
  lt_of_lt_of_le (NodeBank.io rev97m).isLt (Nat.le_add_right _ _)

omit [M8.Machine.Net] in
theorem common_io (roles : Tapes (NodeBank.tapes rev97m) prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (c : Fin CommonBank.K → Option ℕ)
    (st : Tapes 2 prime) :
    (CommonBank.bank roles hs f p node scalar c st).head ⟨(NodeBank.io rev97m).val, io_lt_count⟩ =
      roles.head (NodeBank.io rev97m) ∧
    (CommonBank.bank roles hs f p node scalar c st).tape ⟨(NodeBank.io rev97m).val, io_lt_count⟩ =
      roles.tape (NodeBank.io rev97m) :=
  LeafCore.bank_role roles hs f p node scalar c st (NodeBank.io rev97m)

omit [M8.Machine.Net] in
theorem raw_at {c T : ℕ} (b : Tapes c prime) (i : Fin T) (h : i.val < c) :
    (raw b T).head i = b.head ⟨i.val, h⟩ ∧ (raw b T).tape i = b.tape ⟨i.val, h⟩ := by
  simp [raw, h]

omit [M8.Machine.Net] in
theorem common_setTape (roles : Tapes (NodeBank.tapes rev97m) prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (c : Fin CommonBank.K → Option ℕ)
    (st : Tapes 2 prime) (out : ℤ → Fin (prime+4)) :
    CommonBank.bank (setTape roles (NodeBank.io rev97m) out 0) hs f p node scalar c st =
      setTape (CommonBank.bank roles hs f p node scalar c st) ⟨(NodeBank.io rev97m).val, io_lt_count⟩ out 0 := by
  unfold CommonBank.bank Shared50RecursiveBank.bank
  rw [NodePark.bank_setTape]
  rfl

theorem bankWith_io (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (w : ℕ) (u : Descriptor) (src : ℤ → Fin (prime+4)) :
    (bankWith capacity f p node scalar st w u src).head (ioSlot capacity) = 0 ∧
      (bankWith capacity f p node scalar st w u src).tape (ioSlot capacity) = src := by
  have h := common_io (NodePark.childRoles rev97m src) (Routines.hdr u) f p node scalar
    (Prepare.rest w 529) st
  have hl : (ioSlot capacity).val < CommonBank.count (NodeBank.tapes rev97m) := io_lt_count
  have hraw := raw_at (CommonBank.bank (NodePark.childRoles rev97m src) (Routines.hdr u) f p node scalar
    (Prepare.rest w 529) st) (ioSlot capacity) hl
  unfold bankWith
  rw [hraw.1, hraw.2]
  refine ⟨h.1.trans ?_, h.2.trans ?_⟩ <;> simp [NodePark.childRoles, setTape]

theorem bankWith_set (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (w : ℕ) (u : Descriptor) (src src' : ℤ → Fin (prime+4)) :
    setTape (bankWith capacity f p node scalar st w u src) (ioSlot capacity) src' 0 =
      bankWith capacity f p node scalar st w u src' := by
  unfold bankWith
  rw [AtomRoleSteps.raw_setTape _ (ioSlot capacity) io_lt_count]
  congr 1
  have hr : NodePark.childRoles rev97m src' = setTape (NodePark.childRoles rev97m src) (NodeBank.io rev97m) src' 0 := by
    simp [NodePark.childRoles]
  rw [hr, common_setTape]
  rfl

omit [M8.Machine.Net] in
theorem sourceWord_ext {V : ℕ} {u : Descriptor} (hV : volume prime u = V) (x : Fin V → ZMod 2) :
    sourceWord (v := u) (fun i => ext x i) = sourceWord (v := u) (fun i => x (Fin.cast hV i)) := by
  subst hV
  congr 1
  funext i
  exact Transpose.ext_lt x i

/-- The core's bank on the array `ext x` is its bank with the source word of `x`. -/
theorem bank_eq (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (w : ℕ) (u : Descriptor) (x : Fin (volume prime u) → ZMod 2) :
    Assembly.bank capacity f p node scalar (fun _ => st) w u (ext x) =
      bankWith capacity f p node scalar st w u (sourceWord x) := by
  have h := sourceWord_ext (u := u) rfl x
  unfold Assembly.bank Leaf.leafBank bankWith FamilyStep.rolesAt FamilyRoot.rolesOf
  change raw (CommonBank.bank (NodePark.childRoles rev97m (sourceWord (v := u) fun i => ext x i)) _ _ _ _ _ _ _) _ = _
  rw [h]
  rfl

/-- The core with its I/O role shared with the caller's tape `focus`. -/
def program {t : ℕ} (focus : Fin t) :=
  Placement.placed (CoreRun.program capacity) (SharedPlacementAlphabet.sharedPlacement focus (ioSlot capacity))

/-- **The core on a caller's tape.** -/
theorem runs (hspec : FamilySpec capacity) {K : ℕ} (hK : 2 ≤ K)
    (hs1 : Cost.tauS ≤ M8.Machine.BudgetBound.tau) (hτ₁ : M8.Machine.BudgetBound.tau ≤ 1)
    (hhalf : 1 / 2 ≤ M8.Machine.BudgetBound.tau)
    (h2 : 1 / 2 ≤ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau)
    (hlin : 1 - (K : ℝ)⁻¹ ≤ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau) :
    ∃ C' : ℝ, ∀ v : Descriptor, v.Positive → 2 ≤ v.width →
      rev97m.roleCount ^ RevNode.depth rev97m.width (RevHalf.Rk rev97m) (nOf K v) ∣ v.rows →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ), (∀ z, p ≤ z → f z = blank) →
      ∀ (node : Tapes 1 prime), Family.NodeFree node → ∀ st : Tapes 2 prime,
      RecursiveStackAllocation.Available 0 st → RecursiveStackAllocation.Available 1 st →
      ∀ {t : ℕ} (caller : Tapes t prime) (focus : Fin t) (x : Fin (volume prime v) → ZMod 2),
      caller.tape focus = sourceWord x → caller.head focus = 0 → ∃ c : ℕ,
        (c : ℝ) ≤ C' * volume prime v * (v.width : ℝ) ^ tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau ∧
        HoareTime (program capacity focus)
          (· = caller.append (privateBank capacity f p node st (wOf K v) v))
          (· = (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
            (privateBank capacity f p node st (wOf K v) v)) c := by
  obtain ⟨C', hC'⟩ := CoreRun.core_run capacity hspec hK hs1 hτ₁ hhalf h2 hlin
  refine ⟨C', fun v hp he hrows f p hpay node hfree st hdesc hpc t caller focus x hf hh => ?_⟩
  obtain ⟨c, hc, hH⟩ := hC' v hp he hrows f p hpay node hfree st hdesc hpc x
  rw [bank_eq, bank_eq] at hH
  refine ⟨c, hc, ?_⟩
  have hio := bankWith_io capacity f p node (Place.memo v.width) st (wOf K v) v (sourceWord x)
  have hio' := bankWith_io capacity f p node (Place.memo v.width) st (wOf K v) v
    (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
  have h := SharedPlacementAlphabet.shared_hoare hH caller focus (ioSlot capacity) (fun _ => blank) 0
    (hf.trans hio.2.symm) (hh.trans hio.1.symm)
  rw [bankWith_set, bankWith_set, hio'.1, hio'.2] at h
  exact h

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreShared
