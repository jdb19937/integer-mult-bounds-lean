module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Core
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSteps

/-!
# One run of the reversed family on the core's bank

The core's bank at a view `u` holds the bit array on the `io` role, the headers of `u`, the
family's resting counters `rest w 529` and the caller's stacks (`bankAt`). One family step
pushes the halt code on the PC stack and runs the family's machine (`program`): by the data
semantics of the family (`FamilySpec`) the frame of the pushed bank returns to the halt block
with the reversed interchange of the array and the stack popped, and halts (`family_step`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyStep

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open RecursiveInterchangeLayout (Descriptor volume index)
open SharedPlacementAlphabet (setTape)
open RevMachine
open RevMachine.Family (Frame NodeFree)
open RevMachine.RevHalf (pcs Ok)
open FamilyRoot (ext rolesOf machine entry padded bound FamilySpec impl)
open Core (Step)

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k)

/-- The machine's tapes. -/
abbrev tF := Graph.tapeCount (pcs rev97m) capacity Family.pcSlot Family.pcSlot_pos (impl (k := k))

/-- The roles holding the array `X` of the view `u`. -/
def rolesAt (u : Descriptor) (X : ℕ → ZMod 2) := rolesOf (v := u) (fun i => X i)

/-- **The core's bank** at the view `u`. -/
def bankAt (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (b : ℕ) (u : Descriptor) (X : ℕ → ZMod 2) : Tapes (tF capacity) prime :=
  padded capacity (CommonBank.bank (rolesAt u X) (Routines.hdr u) f p node scalar (Prepare.rest b 529) st)

/-- The PC slot of the machine's tapes. -/
def pcRaw : Fin (tF capacity) :=
  ⟨Family.pcSlot (T := NodeBank.tapes rev97m), lt_of_lt_of_le (Family.pcSlot (T := NodeBank.tapes rev97m)).isLt
    (SharedBankFamily.common_le_tapeCount _)⟩

/-- **One family step**: push the halt code, run the family. -/
def program := Machine.seq (FiniteReturnStackAt.pushProgram (a := prime) (pcRaw capacity)
  (Graph.rootCode (pcs rev97m) capacity)) (machine capacity)

/-- The stack with the halt code pushed. -/
def pushedStack (st : Tapes 2 prime) : Tapes 2 prime :=
  setTape st 1 (FiniteReturnStack.wordPart (st.tape 1) (st.head 1) (Graph.rootCode (pcs rev97m) capacity) k
    le_rfl) (st.head 1 + k)

theorem push_bank (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (b : ℕ) (u : Descriptor) (X : ℕ → ZMod 2) :
    FiniteReturnStackAt.pushed (pcRaw capacity) (Graph.rootCode (pcs rev97m) capacity)
      (bankAt capacity f p node scalar st b u X) =
    padded capacity (CommonBank.bank (rolesAt u X) (Routines.hdr u) f p node scalar (Prepare.rest b 529)
      (pushedStack capacity st)) := by
  have hpc := Family.bank_pc (roles := rolesAt u X) (f := f) (p := p) (node := node) (scalar := scalar)
    (st := st) (Routines.hdr u) (Prepare.rest b 529)
  have hl : (pcRaw capacity).val < Family.count (NodeBank.tapes rev97m) := (Family.pcSlot).isLt
  have hr : ∀ c : Tapes (Family.count (NodeBank.tapes rev97m)) prime,
      (padded capacity c).head (pcRaw capacity) = c.head Family.pcSlot ∧
      (padded capacity c).tape (pcRaw capacity) = c.tape Family.pcSlot := fun c => by
    simp [padded, SharedBankStageInput.raw, pcRaw]
  unfold FiniteReturnStackAt.pushed bankAt
  rw [(hr _).1, (hr _).2, hpc.1, hpc.2]
  unfold padded
  rw [AtomRoleSteps.raw_setTape _ _ hl]
  congr 1
  have := Family.bank_pop (roles := rolesAt u X) (f := f) (p := p) (node := node) (scalar := scalar)
    (st := st) (Routines.hdr u) (Prepare.rest b 529)
    (FiniteReturnStack.wordPart (st.tape 1) (st.head 1) (Graph.rootCode (pcs rev97m) capacity) k le_rfl)
    (st.head 1 + k)
  exact this

omit [M8.Machine.Net] in
theorem rolesAt_ext {u : Descriptor} (y : Fin (volume prime u) → ZMod 2) : rolesAt u (ext y) = rolesOf y := by
  unfold rolesAt
  congr 1
  funext i
  exact Transpose.ext_lt y i

omit [M8.Machine.Net] in
/-- The reversed interchange of the zero extensions holds of every array agreeing below the volume. -/
theorem revT_of_ext {u : Descriptor} {w n : ℕ} (hw : u.width = n * w) {X : ℕ → ZMod 2}
    {x y : Fin (volume prime u) → ZMod 2} (hx : ∀ i : Fin (volume prime u), x i = X i)
    (h : RevT prime w n u (ext x) (ext y)) : RevT prime w n u X (ext y) := by
  intro a ha row hrow before hb h' hh mid hm d hd after haf
  rw [h a ha row hrow before hb h' hh mid hm d hd after haf]
  have hQ : 0 < prime ^ w := pow_pos Networks.Shared50ModularControl.prime_prime.pos w
  have hp : prime ^ (n * w) = prime ^ u.width := by rw [hw]
  have hd' := revAtoms_lt hQ n d
  have hh' := revAtoms_lt hQ n h'
  rw [← pow_mul, Nat.mul_comm w n, hp] at hd' hh'
  have e := Transpose.addr_val (v := u) ⟨a, ha⟩ ⟨row, hrow⟩ ⟨before, hb⟩ ⟨_, hd'⟩ ⟨mid, hm⟩ ⟨_, hh'⟩ ⟨after, haf⟩
  simp only at e
  rw [← e, Transpose.ext_lt, hx]

/-- **One family step** on the core's bank: the reversed interchange of the array, the bank
otherwise restored, within the family bound plus the push. -/
theorem family_step {b₀ : ℕ} (hspec : FamilySpec capacity b₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ((bits b₀).length : ℝ) ≤ L →
      ((max 1 b₀ : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L →
      ∀ (u : Descriptor) (n : ℕ), u.Positive → 0 < b₀ → u.width = n * b₀ → 1 ≤ n →
      rev97m.roleCount ^ RevNode.depth rev97m.width (RevHalf.Rk rev97m) n ∣ u.rows →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ), (∀ z, p ≤ z → f z = blank) →
      ∀ (node : Tapes 1 prime), NodeFree node → ∀ (scalar : Tapes 1 prime) (st : Tapes 2 prime),
      RecursiveStackAllocation.Available 0 st → RecursiveStackAllocation.Available 1 st →
      Core.Step (program capacity) (bankAt capacity f p node scalar st b₀) u u (RevT prime b₀ n u)
        (k + 1 + ⌊bound C L n * volume prime u⌋₊) := by
  obtain ⟨C, hC, hroot⟩ := FamilyRoot.root_hoare capacity hspec
  refine ⟨C, hC, fun L hL hℓ hτ u n hpos hb hw hn hrows f p hpay node hfree scalar st hdesc hpc X => ?_⟩
  set code := Graph.rootCode (pcs rev97m) capacity
  have hcode : Family.Coded (pushedStack capacity st)
      (FiniteReturnStack.address capacity (Graph.encoding (pcs rev97m) .halt)) (st.tape 1) (st.head 1) := by
    refine ⟨by simp [pushedStack, setTape]; rfl, by simp [pushedStack, setTape], fun j _ => hpc _ (by omega)⟩
  let σ : Frame (pcs rev97m) capacity :=
    { v := u, n := n, b := b₀, hpos := hpos, hb := hb, hw := hw, f := f, p := p, node := node,
      scalar := scalar, st := pushedStack capacity st, hfree := hfree, ret := .halt,
      g := st.tape 1, q := st.head 1, hcode := hcode }
  have hok : Ok rev97m b₀ σ :=
    { b := rfl
      rows := hrows
      pay := hpay
      desc := by
        intro z hz
        have : (pushedStack capacity st).head 0 = st.head 0 ∧ (pushedStack capacity st).tape 0 = st.tape 0 := by
          simp [pushedStack, setTape]
        rw [this.2]; rw [this.1] at hz; exact hdesc z hz
      pc := by
        intro z hz
        simp only [σ, pushedStack, setTape, Function.update_self] at hz ⊢
        unfold FiniteReturnStack.wordPart
        rw [dite_eq_right_iff.mpr (fun h => absurd h (by omega))]
        exact hpc z (by omega) }
  have h₂ := hroot L hL hℓ hτ σ hok hn rfl (fun i => X i)
  have h₁ := FiniteReturnStackAt.push_hoare (a := prime) (pcRaw capacity) code (bankAt capacity f p node scalar st b₀ u X)
  refine (h₁.seq (h₂.consequence (fun z hz => ?_) (fun z hz => ?_) le_rfl)).consequence
    (fun _ h => h) (fun _ h => h) le_rfl
  · rw [hz, push_bank]; rfl
  · obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨ext y, revT_of_ext hw (fun _ => rfl) hy, ?_⟩
    unfold bankAt
    rw [rolesAt_ext]
    change padded capacity (CommonBank.bank (rolesOf y) (Routines.hdr u) f p node scalar (Prepare.rest b₀ 529)
      (Family.popped (pushedStack capacity st) (st.tape 1) (st.head 1))) = _
    simp [Family.popped, pushedStack]

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyStep
