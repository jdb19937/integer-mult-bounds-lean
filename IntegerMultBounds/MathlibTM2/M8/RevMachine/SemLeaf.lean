module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCore
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodePark
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemViews

/-!
# The leaves with their data

A frame's role streams are its bits on `io` (`rolesOf`). The leaf core transposes the bits of a
one-atom view (`core_sem`), which is the reversed interchange of one atom pair (`transpose_revT`,
`leafOut_revT`). A leaf of the family runs the core between the same headers and counters as
before (`leaf_runs_of`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open RecursiveInterchangeLayout (Descriptor volume index)
open GraphContract (Runs)
open CommonBank (bank)
open Routines (hdr)
open Blocks (seqB seq_runs runs_mono Leading)
open Family (count leafC NodeFree leafCost)
open NodePark (childRoles)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)

/-! ### Cells -/

theorem index_lt {v : Descriptor} {a row before h mid d after : ℕ} (ha : a < v.beforeRows) (hrow : row < v.rows)
    (hb : before < v.beforeH) (hh : h < prime ^ v.width) (hm : mid < v.between) (hd : d < prime ^ v.width)
    (haf : after < v.afterD) : index prime v a row before h mid d after < volume prime v := by
  have := (RecursiveInterchangeScaling.index (v := v)
    ⟨⟨a, ha⟩, ⟨row, hrow⟩, ⟨before, hb⟩, ⟨h, hh⟩, ⟨mid, hm⟩, ⟨d, hd⟩, ⟨after, haf⟩⟩).isLt
  rwa [RecursiveInterchangeScaling.index_val] at this

/-! ### The leaf's transpose -/

/-- **The transpose of a one-atom view** is its reversed interchange. -/
theorem transpose_revT {u : Descriptor} {b : ℕ} (hw : u.width = 1 * b) (Y : Fin (volume prime u) → ZMod 2) :
    RevT prime b 1 u (ext Y) (ext (Shared50RecursiveNodeRows.transpose (one_dvd u.rows) Y)) := by
  apply revT_one
  intro a ha row hrow before hb h hh mid hm d hd after haf
  have hh' : h < prime ^ u.width := by rw [hw, one_mul]; exact hh
  have hd' : d < prime ^ u.width := by rw [hw, one_mul]; exact hd
  have e1 := index_lt ha hrow hb hh' hm hd' haf
  have e2 := index_lt ha hrow hb hd' hm hh' haf
  have hrow' : row < u.rows / 1 := by rwa [Nat.div_one]
  have key := Shared50RecursiveNodeRows.transpose_address (one_dvd u.rows) Y ⟨a, ha⟩ ⟨row, hrow'⟩ 0
    ⟨before, hb⟩ ⟨d, hd'⟩ ⟨mid, hm⟩ ⟨h, hh'⟩ ⟨after, haf⟩
  have c1 : (⟨index prime u a row before h mid d after, e1⟩ : Fin (volume prime u)) =
      RecursiveInterchangeScaling.index (Shared50RecursiveNodeRows.cyclicAddress (one_dvd u.rows) ⟨a, ha⟩
        ⟨row, hrow'⟩ 0 ⟨before, hb⟩ ⟨h, hh'⟩ ⟨mid, hm⟩ ⟨d, hd'⟩ ⟨after, haf⟩) := by
    apply Fin.ext
    rw [RecursiveInterchangeScaling.index_val]
    simp [Shared50RecursiveNodeRows.cyclicAddress]
  have c2 : (⟨index prime u a row before d mid h after, e2⟩ : Fin (volume prime u)) =
      RecursiveInterchangeScaling.index (Shared50RecursiveNodeRows.cyclicAddress (one_dvd u.rows) ⟨a, ha⟩
        ⟨row, hrow'⟩ 0 ⟨before, hb⟩ ⟨d, hd'⟩ ⟨mid, hm⟩ ⟨h, hh'⟩ ⟨after, haf⟩) := by
    apply Fin.ext
    rw [RecursiveInterchangeScaling.index_val]
    simp [Shared50RecursiveNodeRows.cyclicAddress]
  simp only [ext, e1, e2, ↓reduceDIte]
  rw [c1, c2]
  exact key

/-- The leaf's output on the parent's volume. -/
def leafOut (u : Descriptor) {v : Descriptor} (hvol : volume prime u = volume prime v)
    (Y : Fin (volume prime v) → ZMod 2) : Fin (volume prime v) → ZMod 2 :=
  fun i => Shared50RecursiveNodeRows.transpose (one_dvd u.rows) (fun j => Y (Fin.cast hvol j)) (Fin.cast hvol.symm i)

theorem leafOut_revT {u v : Descriptor} {b : ℕ} (hw : u.width = 1 * b) (hvol : volume prime u = volume prime v)
    (Y : Fin (volume prime v) → ZMod 2) : RevT prime b 1 u (ext Y) (ext (leafOut u hvol Y)) := by
  have h := transpose_revT hw (fun j => Y (Fin.cast hvol j))
  rw [ext_cast] at h
  unfold leafOut
  rw [ext_cast hvol.symm]
  exact h

/-! ### The leaf core on the frame's bits -/

/-- **A frame's role streams**: its bits on `io`, every other role tape blank. -/
def rolesOf (N : RevNetwork) {v : Descriptor} (Y : Fin (volume prime v) → ZMod 2) : Tapes (NodeBank.tapes N) prime :=
  childRoles N (RecursiveShiftRoleBank.source (Shared50RecursiveNodeSemantics.encoded Y))

/-- **The leaf core** transposes the bits of its view. -/
theorem core_sem [M8.Machine.Net] (N : RevNetwork) {v u : Descriptor} (hpos : v.Positive)
    (hvol : volume prime u = volume prime v) (Y : Fin (volume prime v) → ZMod 2) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (c : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    Runs (LeafCore.core (NodeBank.io N)) (bank (rolesOf N Y) (hdr u) f p node scalar c st)
      (bank (rolesOf N (leafOut u hvol Y)) (hdr u) f p node scalar c st) (LeafCore.coreCost (volume prime v) u.width) := by
  have hupos : u.Positive := LeafCore.positive_of_volume
    (hvol ▸ RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le v hpos)
  set y : Fin (volume prime u) → ZMod 2 := fun i => Y (Fin.cast hvol i)
  have hy : (rolesOf N Y).tape (NodeBank.io N) = sourceWord y := by
    simp only [rolesOf, childRoles, setTape, Function.update_self]
    exact (LeafCore.sourceWord_cast hvol Y).symm
  have hh : (rolesOf N Y).head (NodeBank.io N) = 0 := by
    simp [rolesOf, childRoles, setTape]
  set z := Shared50RecursiveNodeRows.transpose (one_dvd u.rows) y
  have hr : setTape (rolesOf N Y) (NodeBank.io N) (sourceWord z) 0 = rolesOf N (leafOut u hvol Y) := by
    simp only [rolesOf, childRoles, SharedPlacementAlphabet.setTape_setTape]
    congr 1
    exact (LeafCore.sourceWord_cast hvol.symm z).symm
  rw [← hr]
  refine Blocks.runs_mono (LeafCore.core_runs _ f p node scalar c st (NodeBank.io N) hupos y hh hy) ?_
  rw [← hvol]
  exact LeafCore.cost_le hupos

/-! ### A leaf of the family -/

variable {T : ℕ} {f : ℤ → Fin (prime+4)} {p : ℤ} {node scalar : Tapes 1 prime} {st : Tapes 2 prime}

/-- **A leaf** from `r ≥ 1` remaining leaves to `r - 1`, with the core's run on the leaf view. -/
theorem leaf_runs_of {core : Graph.Block (count T) prime} (hlead : Leading core) {coreCost : ℕ → ℕ → ℕ}
    {v : Descriptor} {b m n r : ℕ} (hpos : v.Positive) (hb : 0 < b) (hw : v.width = n * b) (hr : 1 ≤ r)
    (hrn : r ≤ n) (hfree : NodeFree node) {roles roles' : Tapes T prime}
    (hcore : ∀ (node' : Tapes 1 prime) (c' : Fin CommonBank.K → Option ℕ),
      Runs core (bank roles (hdr (RevMachine.sub prime b n (r - 1) 1 v)) f p node' scalar c' st)
        (bank roles' (hdr (RevMachine.sub prime b n (r - 1) 1 v)) f p node' scalar c' st) (coreCost (volume prime v) b)) :
    Runs (Family.leaf core) (bank roles (hdr v) f p node scalar (leafC b m n r) st)
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
  have h₄ := hcore (RecursiveViewFrame.savedStack (hdr v) node) c₁
  rw [← hu] at h₄
  have h₅ := Blocks.restore_runs roles' (Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1))
    f p node scalar c₁ st (hdr v) (Family.nodeFree_free hfree _)
  obtain ⟨B₆, hB₆, h₆⟩ := LeafRoutines.advance_runs (roles := roles') (hs := hdr v) (f := f) (p := p)
    (node := node) (scalar := scalar) (st := st) (c := c₁) (n := n) (r := r) (s := r - 1) (cc := 1)
    (e := n - (r - 1) - 1) hrn (by omega) (by omega) (by omega)
    (by simp [c₁, leafC]) (by simp [c₁]) (by simp [c₁]) (by simp [c₁])
  have hc : Function.update (Function.update (Function.update (Function.update c₁ 11 (some (r - 1))) 12 none)
      13 none) 14 none = leafC b m n (r - 1) := by
    funext j; fin_cases j <;> rfl
  rw [hc] at h₆
  have hp := RecursiveViewFrame.pushCost_le (hdr v) (Family.hlen v)
    (fun z => RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le v hpos _
      (Routines.hdr_headers v) z)
  have hq := RecursiveViewFrame.restoreCost_le (hdr v)
    (Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1)) (Family.hlen v)
    (fun z => RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le v hpos _
      (Routines.hdr_headers v) z)
    (fun z => by
      rw [hu]
      have := RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le u
        (Family.sub_positive hpos) _ (Routines.hdr_headers u) z
      rwa [hvol] at this)
  have L5 := seq_runs (fun _ => rfl) (fun _ => rfl) h₅ h₆
  have L4 := seq_runs hlead (fun _ => rfl) h₄ L5
  have L3 := seq_runs (fun _ => rfl) (fun _ => rfl) h₃ L4
  have L2 := seq_runs (fun _ => rfl) (fun _ => rfl) h₂ L3
  have L1 := seq_runs (fun _ => rfl) (fun _ => rfl) h₁ L2
  exact runs_mono L1 (by unfold leafCost; omega)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics
