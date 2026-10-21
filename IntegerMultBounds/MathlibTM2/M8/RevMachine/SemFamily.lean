module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemHalf

/-!
# The block invariants of the stage-2 PR97 family with its data

A frame with its input bits (`SFrame`): the graph's blocks carry the frame's bits through the
leaves, the node and the finish (`semInv`), so a frame exits with the reversed interchange of its
input on `io`:

* after `i` leaves, the bits are the reversed interchange of the input on the view of the last `i`
  remainder atoms (`revT_grow`);
* the node runs on the leaves' output, and returns the reversed interchange of the middle view
  (`merge_sem`), so of the whole field (`revT_partition`);
* a block call enters a child frame on its wire's bits, whose exit is their reversed interchange.

The blocks and their costs are those of `Family.inv` for `Rev97Node.half97` (`ownCost_eq`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics

noncomputable section
open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open GraphContract (Runs Tests Pops)
open CommonBank (bank)
open Routines (hdr)
open RecursiveInterchangeLayout (Descriptor volume)
open NodeSplit (midView)
open Family (Frame leafC prepCost leafCost finishCost)
open RevHalf (pcs Ok)

variable {k : ℕ} (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k)

/-- A frame with its input bits. -/
structure SFrame where
  σ : Frame (pcs rev97m) capacity
  X : Fin (volume prime σ.v) → ZMod 2

variable {capacity}

/-- The implementation of the stage-2 PR97 family. -/
abbrev impl97 [M8.Machine.Net] (k : ℕ) :=
  Family.impl (T := NodeBank.tapes rev97m) (k := k) (LeafCore.core (NodeBank.io rev97m)) (RevNode.blocks rev97m k)

theorem leading97 [M8.Machine.Net] : Blocks.Leading (LeafCore.core (T := NodeBank.tapes rev97m) (NodeBank.io rev97m)) :=
  Blocks.place_leading _ _ _ _

/-- **A leaf** with its data. -/
theorem leaf_sem [M8.Machine.Net] (S : SFrame capacity) (i : ℕ) (hi : i < S.σ.n % rev97m.width)
    (Y : Fin (volume prime S.σ.v) → ZMod 2)
    (hY : RevT prime S.σ.b i (RevMachine.sub prime S.σ.b S.σ.n (S.σ.n % rev97m.width - i) i S.σ.v) (ext S.X) (ext Y)) :
    ∃ Y' : Fin (volume prime S.σ.v) → ZMod 2, RevT prime S.σ.b (i + 1) (RevMachine.sub prime S.σ.b S.σ.n (S.σ.n % rev97m.width - (i + 1)) (i + 1) S.σ.v)
        (ext S.X) (ext Y') ∧
      Runs (Family.leaf (LeafCore.core (NodeBank.io rev97m)))
        (S.σ.at (rolesOf rev97m Y) (leafC S.σ.b rev97m.width S.σ.n (S.σ.n % rev97m.width - i)))
        (S.σ.at (rolesOf rev97m Y') (leafC S.σ.b rev97m.width S.σ.n (S.σ.n % rev97m.width - (i + 1))))
        (leafCost LeafCore.coreCost S.σ.v S.σ.b S.σ.n) := by
  set δ := S.σ.n % rev97m.width
  have hδ : δ ≤ S.σ.n := Nat.mod_le _ _
  set r := δ - i
  have hr : 1 ≤ r := by omega
  set u := RevMachine.sub prime S.σ.b S.σ.n (r - 1) 1 S.σ.v
  have hvol : volume prime u = volume prime S.σ.v := RevMachine.sub_volume prime S.σ.b S.σ.n (r - 1) 1 S.σ.v S.σ.hw (by omega)
  refine ⟨leafOut u hvol Y, ?_, ?_⟩
  · have h₂ := leafOut_revT (b := S.σ.b) (rfl : u.width = 1 * S.σ.b) hvol Y
    have h₁ : RevT prime S.σ.b i (RevMachine.sub prime S.σ.b S.σ.n (r - 1 + 1) i S.σ.v) (ext S.X) (ext Y) := by
      rw [Nat.sub_add_cancel hr]; exact hY
    have h := revT_grow (k := r - 1) (Networks.Shared50ModularControl.prime_prime.pos) (by omega) h₁ h₂
    rwa [show r - 1 = δ - (i + 1) by omega] at h
  · have h := leaf_runs_of (f := S.σ.f) (p := S.σ.p) (scalar := S.σ.scalar) (st := S.σ.st) (m := rev97m.width)
      leading97 S.σ.hpos S.σ.hb S.σ.hw hr (by omega) S.σ.hfree (roles := rolesOf rev97m Y)
      (roles' := rolesOf rev97m (leafOut u hvol Y)) (coreCost := LeafCore.coreCost) (fun node' c' => by
        have := core_sem rev97m S.σ.hpos hvol Y S.σ.f S.σ.p node' S.σ.scalar c' S.σ.st
        rwa [show u.width = S.σ.b from one_mul _] at this)
    rw [show r - 1 = δ - (i + 1) by omega] at h
    exact h

/-- **The block invariants with data.** -/
def semInv [M8.Machine.Net] (b₀ : ℕ) :
    GraphExists.Inv (pcs rev97m) capacity (Family.pcSlot (T := NodeBank.tapes rev97m)) (impl97 k) rev97m.width
      rev97m.roleCount Prod.snd where
  Shape := SFrame capacity
  size S := S.σ.n
  vol S := volume prime S.σ.v
  ret S := S.σ.ret
  leaves S := S.σ.n % rev97m.width
  Entry S x₀ := Ok rev97m b₀ S.σ ∧ x₀ = S.σ.at (rolesOf rev97m S.X) (Prepare.rest S.σ.b rev97m.width)
  Leaf S _ i y := ∃ Y : Fin (volume prime S.σ.v) → ZMod 2,
    y = S.σ.at (rolesOf rev97m Y) (leafC S.σ.b rev97m.width S.σ.n (S.σ.n % rev97m.width - i)) ∧
      RevT prime S.σ.b i (RevMachine.sub prime S.σ.b S.σ.n (S.σ.n % rev97m.width - i) i S.σ.v) (ext S.X) (ext Y)
  Node S _ i y := ∃ YL : Fin (volume prime S.σ.v) → ZMod 2,
    RevT prime S.σ.b (S.σ.n % rev97m.width) (RevMachine.sub prime S.σ.b S.σ.n 0 (S.σ.n % rev97m.width) S.σ.v)
      (ext S.X) (ext YL) ∧ NodeSem S.σ YL i y
  Done S _ y := ∃ Y : Fin (volume prime S.σ.v) → ZMod 2,
    y = S.σ.at (rolesOf rev97m Y) (leafC S.σ.b rev97m.width S.σ.n 0) ∧ RevT prime S.σ.b S.σ.n S.σ.v (ext S.X) (ext Y)
  Finished S _ y := ∃ Y : Fin (volume prime S.σ.v) → ZMod 2,
    y = S.σ.at (rolesOf rev97m Y) (Prepare.rest S.σ.b rev97m.width) ∧ RevT prime S.σ.b S.σ.n S.σ.v (ext S.X) (ext Y)
  Exit S _ z := ∃ Y : Fin (volume prime S.σ.v) → ZMod 2,
    z = S.σ.exitAt (rolesOf rev97m Y) rev97m.width ∧ RevT prime S.σ.b S.σ.n S.σ.v (ext S.X) (ext Y)
  cPrepare S := prepCost S.σ.b rev97m.width S.σ.n
  cTest _ := 1
  cLeaf S := leafCost LeafCore.coreCost S.σ.v S.σ.b S.σ.n
  cSplit S := NodeSplit.splitCost (N := rev97m) S.σ.v S.σ.b S.σ.n
  cMerge S := NodeSplit.mergeCost (N := rev97m) S.σ.v S.σ.b S.σ.n
  cFinish S := finishCost rev97m.width S.σ.n
  cSeg S := RevHalf.segCost rev97m S.σ
  cCall S := RevHalf.callCost rev97m S.σ
  prepare S x₀ := by
    rintro ⟨-, rfl⟩
    exact ⟨_, ⟨S.X, by rw [Nat.sub_zero]; rfl, revT_zero _ _ _ _⟩,
      Family.prepare_runs S.σ.hb Rev97Node.width97_pos S.σ.hw⟩
  test_leaf S x₀ i y _ hi := by
    rintro ⟨Y, rfl, -⟩
    obtain ⟨st', he, hr, hh⟩ := Family.test_runs (roles := rolesOf rev97m Y) (f := S.σ.f) (p := S.σ.p)
      (node := S.σ.node) (scalar := S.σ.scalar) (st := S.σ.st) (b := S.σ.b) (m := rev97m.width) (n := S.σ.n)
      (r := S.σ.n % rev97m.width - i) Rev97Node.width97_pos (hdr S.σ.v)
    refine ⟨1, le_rfl, st', he.trans ?_, hr, hh⟩
    rw [ite_eq_left (by omega)]
  test_end S x₀ y _ := by
    rintro ⟨Y, rfl, -⟩
    obtain ⟨st', he, hr, hh⟩ := Family.test_runs (roles := rolesOf rev97m Y) (f := S.σ.f) (p := S.σ.p)
      (node := S.σ.node) (scalar := S.σ.scalar) (st := S.σ.st) (b := S.σ.b) (m := rev97m.width) (n := S.σ.n)
      (r := S.σ.n % rev97m.width - S.σ.n % rev97m.width) Rev97Node.width97_pos (hdr S.σ.v)
    refine ⟨1, le_rfl, st', he.trans ?_, hr, hh⟩
    rw [ite_eq_right (by omega)]
  leaf S x₀ i y _ hi := by
    rintro ⟨Y, rfl, hY⟩
    obtain ⟨Y', hY', h⟩ := leaf_sem S i hi Y hY
    exact ⟨_, ⟨Y', rfl, hY'⟩, h⟩
  split S x₀ y hx hm' := by
    rintro ⟨Y, rfl, hY⟩
    rw [Nat.sub_self] at hY ⊢
    obtain ⟨y', hy', hr⟩ := split_sem S.σ hx.1 hm' Y
    exact ⟨y', ⟨Y, hY, hy'⟩, hr⟩
  seg S x₀ y hx hm' i s hi := by
    rintro ⟨YL, hYL, hy⟩
    obtain ⟨y', hy', hr⟩ := seg_sem S.σ YL y hx.1 hm' i s hi hy
    exact ⟨y', ⟨YL, hYL, hy'⟩, hr⟩
  call S x₀ y hx hm' i c hi := by
    rintro ⟨YL, hYL, hy⟩
    obtain ⟨τ, hτok, hn, hv, hret, -, Xτ, E, R, hER, he, hrec⟩ := call_sem S.σ YL y hx.1 hm' i c hi hy
    refine ⟨⟨τ, Xτ⟩, _, hn, hv, hret, ⟨hτok, rfl⟩, E, R, hER, he, ?_⟩
    rintro z ⟨Y, rfl, hT⟩
    obtain ⟨y', hy', hr⟩ := hrec Y hT
    exact ⟨y', ⟨YL, hYL, hy'⟩, hr⟩
  merge S x₀ y hx hm' := by
    rintro ⟨YL, hYL, hy⟩
    obtain ⟨Y, hT, hr⟩ := merge_sem S.σ YL y hx.1 hm' hy
    refine ⟨_, ⟨Y, rfl, ?_⟩, hr⟩
    have hsum := NodeSplit.mid_sum rev97m S.σ.n
    have hT' : RevT prime S.σ.b (S.σ.n - S.σ.n % rev97m.width)
        (RevMachine.sub prime S.σ.b S.σ.n (S.σ.n % rev97m.width) (S.σ.n - S.σ.n % rev97m.width) S.σ.v)
        (ext YL) (ext Y) := by
      have e : S.σ.n - S.σ.n % rev97m.width = rev97m.width * (S.σ.n / rev97m.width) := by omega
      rw [e]; exact hT
    exact revT_partition Networks.Shared50ModularControl.prime_prime.pos S.σ.hw (Nat.mod_le _ _) hYL hT'
  done_leaf S x₀ y _ hm' := by
    rintro ⟨Y, rfl, hY⟩
    have hδ : S.σ.n % rev97m.width = S.σ.n := Nat.mod_eq_of_lt (by omega)
    refine ⟨Y, by rw [Nat.sub_self], ?_⟩
    rw [Nat.sub_self, hδ, sub_all _ _ _ _ S.σ.hw] at hY
    exact hY
  finish S x₀ y _ := by
    rintro ⟨Y, rfl, hY⟩
    have h := Prepare.finish_runs (roles := rolesOf rev97m Y) (hs := hdr S.σ.v) (f := S.σ.f) (p := S.σ.p)
      (node := S.σ.node) (scalar := S.σ.scalar) (st := S.σ.st) (c := leafC S.σ.b rev97m.width S.σ.n 0)
      (f' := S.σ.n / rev97m.width) (n := S.σ.n) (r := 0) (by simp [leafC]) (by simp [leafC]) (by simp [leafC])
    rw [Family.finish_counters] at h
    exact ⟨_, ⟨Y, rfl, hY⟩, h⟩
  pop S x₀ y _ := by
    rintro ⟨Y, rfl, hY⟩
    obtain ⟨hc, hh, hf⟩ := S.σ.hcode
    refine ⟨_, ⟨Y, rfl, hY⟩, S.σ.g, S.σ.q, ?_, ?_, hf, ?_⟩
    · simp only [Frame.at]; rw [(Family.bank_pc _ _).2]; exact hc
    · simp only [Frame.at]; rw [(Family.bank_pc _ _).1]; exact hh
    · simp only [Frame.at, Frame.exitAt]; exact Family.bank_pop _ _ _ _

/-- The frames' own costs are those of the cost-only invariants. -/
theorem ownCost_eq [M8.Machine.Net] (b₀ : ℕ) (S : SFrame capacity) :
    (semInv (capacity := capacity) b₀).ownCost S =
      (Family.inv (Rev97Node.leafCore rev97m) Rev97Node.width97_pos (Rev97Node.half97 b₀ capacity)).ownCost S.σ := rfl

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics
