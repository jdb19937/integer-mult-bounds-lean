module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafRoutines
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Guard

/-!
# The reversed family on the common bank

A frame (`Frame`) is a call on a view `v` of `n` atoms of `b` digits, with its node stack, scalar
stack, payload work tapes and call stacks, and the return address whose code tops the PC stack.
Its role streams are free, up to a shape `Good` that every block keeps.

The preparation (`Prepare.atoms`, `Prepare.divide`), the test (`Guard`), the leaves and the
finish are concrete blocks. A leaf computes its offsets, saves the headers on the node stack,
installs the headers of `sub (r-1) 1`, runs the leaf core, restores the headers and counts one
leaf fewer (`leaf_runs`). The leaf core is a hypothesis (`LeafCore`): on any one-atom view it
runs from good role streams to good role streams within `coreCost`. The node's blocks (split,
pieces, merge) are an interface (`NodeHalf`): shapes for the node's banks and runs between them.

`inv` assembles `GraphExists.Inv`, so `GraphExists.contract` gives the family's contract.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Family

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs Tests Pops)
open CommonBank (bank Target word K)
open Routines (hdr)
open Blocks (seqB seq_runs runs_mono Leading)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)

variable {T : ℕ}

abbrev count (T : ℕ) := CommonBank.count T

/-- The PC stack. -/
def pcSlot : Fin (count T) := Shared50RecursiveBank.returnSlot 1

theorem pcSlot_pos : 0 < count T := Nat.zero_lt_of_lt (pcSlot (T := T)).isLt

/-- The counters during the leaf loop, with `r` leaves remaining. -/
def leafC (b m n r : ℕ) : Fin K → Option ℕ :=
  Function.update (Function.update (Function.update (Prepare.rest b m) 9 (some n)) 5 (some (n / m))) 11
    (some r)

/-! ### The concrete blocks -/

def prepare : Graph.Block (count T) prime := seqB Prepare.atoms Prepare.divide

def test : Graph.Block (count T) prime :=
  SharedBankFamily.ofProgram (s := 0)
    (Guard.program (a := prime) (Fin.castAdd 0 (CommonBank.auxSlot (t := T) 11))
      (Fin.castAdd 0 (CommonBank.auxSlot (t := T) 5)))

def leaf (core : Graph.Block (count T) prime) : Graph.Block (count T) prime :=
  seqB LeafRoutines.offsets (seqB Blocks.push (seqB LeafRoutines.view (seqB core
    (seqB Blocks.restore LeafRoutines.advance))))

/-- The leaf core runs on any one-atom view from good role streams to good role streams. -/
def LeafCore (core : Graph.Block (count T) prime) (Good : Descriptor → Tapes T prime → Prop)
    (coreCost : ℕ → ℕ → ℕ) : Prop :=
  Leading core ∧ ∀ (v u : Descriptor) (b : ℕ), RecursiveDimensionBank.Headers u (hdr u) →
    u.width = b → volume prime u = volume prime v → ∀ (hs : Fin 6 → List Bool), hs = hdr u →
    ∀ roles f p node scalar c st, Good v roles → ∃ roles', Good v roles' ∧
      Runs core (bank roles hs f p node scalar c st) (bank roles' hs f p node scalar c st) (coreCost (volume prime v) b)

/-! ### The runs of the concrete blocks -/

variable {roles : Tapes T prime} {f : ℤ → Fin (prime+4)} {p : ℤ} {node scalar : Tapes 1 prime}
  {st : Tapes 2 prime}

theorem hdr_width (v : Descriptor) : Counter.value (hdr v 3) = v.width :=
  FlatCoordinateSchedule.bits_value _

/-- The preparation's cost. -/
def prepCost (b m n : ℕ) : ℕ :=
  (BinaryDescriptorDivMod.linearConstant (bits b) * (n * b + 1) + 2 * b + 6) +
    BinaryDescriptorDivMod.linearConstant (bits m) * (n + 1) + 1

/-- **The preparation**: `n` atoms, `⌊n/m⌋` per coordinate, `n mod m` leaves remaining. -/
theorem prepare_runs {v : Descriptor} {b m n : ℕ} (hb : 0 < b) (hm : 0 < m) (hw : v.width = n * b) :
    Runs prepare (bank roles (hdr v) f p node scalar (Prepare.rest b m) st)
      (bank roles (hdr v) f p node scalar (leafC b m n (n % m)) st) (prepCost b m n) := by
  obtain ⟨B₁, hB₁, h₁⟩ := Prepare.atoms_runs (roles := roles) (f := f) (p := p) (node := node)
    (scalar := scalar) (st := st) (c := Prepare.rest b m) (hs := hdr v) hb (hdr_width v)
    (FlatCoordinateSchedule.bits_canonical _) rfl rfl
  rw [hw, Nat.mul_div_cancel _ hb] at h₁
  obtain ⟨B₂, hB₂, h₂⟩ := Prepare.divide_runs (roles := roles) (f := f) (p := p) (node := node)
    (scalar := scalar) (st := st) (hs := hdr v) (c := Function.update (Prepare.rest b m) 9 (some n)) (n := n) (m := m)
    hm (by simp) (by simp [Prepare.rest]) (by simp [Prepare.rest]) (by simp [Prepare.rest])
  rw [hw] at hB₁
  exact runs_mono (seq_runs (fun _ => rfl) (fun _ => rfl) h₁ h₂)
    (by unfold prepCost; omega)

/-- The test on a bank of the leaf loop. -/
theorem test_runs {b m n r : ℕ} (hm : 0 < m) (hs : Fin 6 → List Bool) :
    ∃ st' : Fin (test (T := T)).states,
      Guard.exit st' = (if r ≠ 0 then .leaf else if m ≤ n then .node else .done) ∧
      run (test (T := T)).program 1 ((raw (bank roles hs f p node scalar (leafC b m n r) st)
        (test (T := T)).tapes).start (test (T := T)).program) =
        some (SharedBankFamilyExact.atState (raw (bank roles hs f p node scalar (leafC b m n r) st)
          (test (T := T)).tapes) st') ∧
      step (test (T := T)).program (SharedBankFamilyExact.atState (raw (bank roles hs f p node scalar
        (leafC b m n r) st) (test (T := T)).tapes) st') = none := by
  set x := raw (bank roles hs f p node scalar (leafC b m n r) st) (count T + 0)
  obtain ⟨hr, hh⟩ := Guard.run_exact (Fin.castAdd 0 (CommonBank.auxSlot (t := T) 11))
    (Fin.castAdd 0 (CommonBank.auxSlot (t := T) 5)) x
  refine ⟨_, ?_, hr, hh⟩
  have r11 := CommonBank.bank_aux roles hs f p node scalar (leafC b m n r) st 11
  have r5 := CommonBank.bank_aux roles hs f p node scalar (leafC b m n r) st 5
  have l11 := Embed.raw_left (p := 0) (bank roles hs f p node scalar (leafC b m n r) st) (CommonBank.auxSlot 11)
  have l5 := Embed.raw_left (p := 0) (bank roles hs f p node scalar (leafC b m n r) st) (CommonBank.auxSlot 5)
  have c11 : leafC b m n r 11 = some r := by simp [leafC]
  have c5 : leafC b m n r 5 = some (n / m) := by simp [leafC]
  rw [c11] at r11; rw [c5] at r5
  have b11 := Blocks.counter_blank r
  have b5 := Blocks.counter_blank (n / m)
  have hdiv : n / m ≠ 0 ↔ m ≤ n := by
    rw [ne_eq, Nat.div_eq_zero_iff]; omega
  unfold Guard.result
  simp only [x, l11.1, l11.2, l5.1, l5.2, r11.1, r11.2, r5.1, r5.2, word, Option.map_some]
  by_cases h1 : r ≠ 0
  · rw [if_pos (b11.mpr h1), if_pos h1]; rfl
  · rw [if_neg (fun h => h1 (b11.mp h)), if_neg h1]
    by_cases h2 : m ≤ n
    · rw [if_pos (b5.mpr (hdiv.mpr h2)), if_pos h2]; rfl
    · rw [if_neg (fun h => h2 (hdiv.mp (b5.mp h))), if_neg h2]; rfl

theorem sub_positive {v : Descriptor} {b n s c : ℕ} (hpos : v.Positive) :
    (RevMachine.sub prime b n s c v).Positive := by
  have hq0 : 0 < prime := Networks.Shared50ModularControl.prime_prime.pos
  obtain ⟨hA, hR, hB, hC, hE⟩ := hpos
  exact ⟨hA, hR, Nat.mul_pos hB (pow_pos hq0 _),
    Nat.mul_pos (Nat.mul_pos (pow_pos hq0 _) hC) (pow_pos hq0 _), Nat.mul_pos (pow_pos hq0 _) hE⟩

/-- A node stack with free cells from its head on. -/
def NodeFree (node : Tapes 1 prime) : Prop := ∀ z, node.head 0 ≤ z → node.tape 0 z = blank

theorem nodeFree_free {node : Tapes 1 prime} (h : NodeFree node) (hs : Fin 6 → List Bool) :
    RecursiveViewFrame.Free hs node := fun z hz _ => h z hz

/-- The header length bound of a view. -/
def hlen (v : Descriptor) : ℕ := Nat.log2 (volume prime v) + 1

/-- A leaf's cost. -/
def leafCost (coreCost : ℕ → ℕ → ℕ) (v : Descriptor) (b n : ℕ) : ℕ :=
  (30 * n + 130) + (12 * hlen v + 48) + 1500 * volume prime v + coreCost (volume prime v) b +
    (24 * hlen v + 79) + (20 * n + 40) + 5

/-- **A leaf**: from `r ≥ 1` remaining leaves to `r - 1`, with the role streams run by the core. -/
theorem leaf_runs {core : Graph.Block (count T) prime} {Good : Descriptor → Tapes T prime → Prop}
    {coreCost : ℕ → ℕ → ℕ} (hcore : LeafCore core Good coreCost) {v : Descriptor} {b m n r : ℕ}
    (hpos : v.Positive) (hb : 0 < b) (hw : v.width = n * b) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hfree : NodeFree node) (hg : Good v roles) :
    ∃ roles', Good v roles' ∧ Runs (leaf core) (bank roles (hdr v) f p node scalar (leafC b m n r) st)
      (bank roles' (hdr v) f p node scalar (leafC b m n (r - 1)) st) (leafCost coreCost v b n) := by
  set c₁ := Function.update (Function.update (Function.update (leafC b m n r) 12 (some (r - 1)))
    13 (some 1)) 14 (some (n - (r - 1) - 1))
  obtain ⟨B₁, hB₁, h₁⟩ := LeafRoutines.offsets_runs (roles := roles) (hs := hdr v) (f := f) (p := p)
    (node := node) (scalar := scalar) (st := st) (c := leafC b m n r) hr hrn
    (by simp [leafC]) (by simp [leafC]) (by simp [leafC, Prepare.rest]) (by simp [leafC, Prepare.rest])
    (by simp [leafC, Prepare.rest]) (by simp [leafC, Prepare.rest])
  have h₂ := Blocks.push_runs roles (hdr v) f p node scalar c₁ st
  have h₃ := LeafRoutines.view_runs (roles := roles) (f := f) (p := p)
    (node := RecursiveViewFrame.savedStack (hdr v) node) (scalar := scalar) (st := st) (c := c₁)
    (Routines.hdr_headers v) hpos hb hw (s := r - 1) (cc := 1) (by omega) rfl
    (by simp [c₁, leafC, Prepare.rest]) (by simp [c₁]) (by simp [c₁]) (by simp [c₁])
  set u := RevMachine.sub prime b n (r - 1) 1 v
  have hu : Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1) = hdr u :=
    Routines.hdr_eq (Headers.child_headers (Routines.hdr_headers v) rfl)
  have hvol : volume prime u = volume prime v := RevMachine.sub_volume prime b n (r - 1) 1 v hw (by omega)
  obtain ⟨roles', hg', h₄⟩ := hcore.2 v u b (hu ▸ Headers.child_headers (Routines.hdr_headers v) rfl)
    (by simp [u, RevMachine.sub]) hvol _ hu roles f p (RecursiveViewFrame.savedStack (hdr v) node) scalar c₁ st hg
  have h₅ := Blocks.restore_runs roles' (Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1))
    f p node scalar c₁ st (hdr v) (nodeFree_free hfree _)
  obtain ⟨B₆, hB₆, h₆⟩ := LeafRoutines.advance_runs (roles := roles') (hs := hdr v) (f := f) (p := p)
    (node := node) (scalar := scalar) (st := st) (c := c₁) (n := n) (r := r) (s := r - 1) (cc := 1)
    (e := n - (r - 1) - 1) hrn (by omega) (by omega) (by omega)
    (by simp [c₁, leafC]) (by simp [c₁]) (by simp [c₁]) (by simp [c₁])
  have hc : Function.update (Function.update (Function.update (Function.update c₁ 11 (some (r - 1))) 12 none)
      13 none) 14 none = leafC b m n (r - 1) := by
    funext j; fin_cases j <;> first | rfl | simp [c₁, leafC, Prepare.rest, Function.update]
  rw [hc] at h₆
  refine ⟨roles', hg', ?_⟩
  have hp := RecursiveViewFrame.pushCost_le (hdr v) (hlen v)
    (fun z => RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le v hpos _
      (Routines.hdr_headers v) z)
  have hq := RecursiveViewFrame.restoreCost_le (hdr v)
    (Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1)) (hlen v)
    (fun z => RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le v hpos _
      (Routines.hdr_headers v) z)
    (fun z => by
      rw [hu]
      have := RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le u
        (sub_positive hpos) _ (Routines.hdr_headers u) z
      rwa [hvol] at this)
  have L5 := seq_runs (fun _ => rfl) (fun _ => rfl) h₅ h₆
  have L4 := seq_runs hcore.1 (fun _ => rfl) h₄ L5
  have L3 := seq_runs (fun _ => rfl) (fun _ => rfl) h₃ L4
  have L2 := seq_runs (fun _ => rfl) (fun _ => rfl) h₂ L3
  have L1 := seq_runs (fun _ => rfl) (fun _ => rfl) h₁ L2
  exact runs_mono L1 (by unfold leafCost; omega)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
