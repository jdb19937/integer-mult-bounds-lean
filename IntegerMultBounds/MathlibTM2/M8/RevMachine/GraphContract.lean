module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Contract

/-!
# The contract of the control graph

The graph's runs close the family's recursion. A specification (`Spec`) names the frames of the
family, each a call of `size` atoms with its volume, return address, and the banks at its entry
and its return, and gives every block's run between the banks of a frame: the preparation, the
test and the leaves of the leaf loop, the node's split, its pieces and merge, the finish and the
pop. At a block call of rank `r` it gives the child frame, of `r ⌊n/m⌋` atoms on `1/W` of the
volume, whose return is the call site's recovery block.

`frame_run`: if the children meet the contract at costs `T`, a frame runs from the graph's entry
to its return address within its own blocks' cost plus `Σ_r T(r⌊n/m⌋)/W` of its volume. So
`contract` is `RevMachine.family_contract` on the graph's runs: when the frames' own work is at
most `C L` of the volume below the cutoff and `C n + C L` above it, every frame of `n` atoms runs
within `C/(1-q₁) n + C/(1-q_τ) n^τ L` of its volume.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphContract

noncomputable section
open IntegerMultBounds.Machine
open Graph GraphRun
open SharedBankStageInput (raw)
open SharedBankFamilyExact (atState)
open SharedPlacementAlphabet (setTape)

/-- A function on pieces, by cases. -/
def segCall {Seg Call : Type} (f : Seg → ℝ) (g : Call → ℝ) : Piece Seg Call → ℝ
  | .seg s => f s
  | .call c => g c

/-- The ranks of the schedule's block calls, in order. -/
def ranks {Seg Call : Type} (rank : Call → ℕ) : List (Piece Seg Call) → List ℕ
  | [] => []
  | .seg _ :: ps => ranks rank ps
  | .call c :: ps => rank c :: ranks rank ps

theorem rank_mem {Seg Call : Type} (rank : Call → ℕ) : ∀ (ps : List (Piece Seg Call)) (i : ℕ)
    (hi : i < ps.length) (c : Call), ps[i] = .call c → rank c ∈ ranks rank ps
  | [], _, hi, _, _ => absurd hi (by simp)
  | p :: ps, 0, _, c, h => by
    simp only [List.getElem_cons_zero] at h
    subst h
    exact List.mem_cons_self
  | p :: ps, i+1, hi, c, h => by
    simp only [List.getElem_cons_succ] at h
    have := rank_mem rank ps i (by simpa using hi) c h
    cases p with
    | seg _ => exact this
    | call _ => exact List.mem_cons_of_mem _ this

/-- The calls' terms of a schedule sum over its ranks. -/
theorem sum_calls {Seg Call : Type} (rank : Call → ℕ) (g : ℕ → ℝ) (a : Seg → ℝ) (b : Call → ℝ) :
    ∀ ps : List (Piece Seg Call),
      (ps.map (segCall a fun c => b c + g (rank c))).sum =
        (ps.map (segCall a b)).sum + ((ranks rank ps).map g).sum
  | [] => by simp [ranks]
  | .seg s :: ps => by
    simp only [List.map_cons, List.sum_cons, ranks, segCall, sum_calls rank g a b ps]; ring
  | .call c :: ps => by
    simp only [List.map_cons, List.sum_cons, ranks, segCall, sum_calls rank g a b ps]; ring

variable {Seg Call : Type} {t a k : ℕ} (pieces : List (Piece Seg Call))
  (capacity : Fintype.card (PC pieces.length) ≤ 2^k) (stack : Fin t) (ht : 0 < t)
  (impl : Implementation t a k Seg Call)

/-- A clean block run from the bank `x` to the bank `y`. -/
abbrev Runs (b : Block t a) (x y : Tapes t a) (B : ℕ) : Prop :=
  HoareTime b.program (fun w => w = raw x b.tapes) (fun w => w = raw y b.tapes) B

/-- The test keeps the bank `x` and ends in a terminal state of exit `e`. -/
def Tests (x : Tapes t a) (e : Exit) (B : ℕ) : Prop :=
  ∃ n ≤ B, ∃ st : Fin impl.test.states, impl.exit st = e ∧
    run impl.test.program n ((raw x impl.test.tapes).start impl.test.program) =
      some (atState (raw x impl.test.tapes) st) ∧
    step impl.test.program (atState (raw x impl.test.tapes) st) = none

/-- The bank `x` has the code of `pc` on top of the return stack, and erasing it leaves `y`. -/
def Pops (x : Tapes t a) (pc : PC pieces.length) (y : Tapes t a) : Prop :=
  ∃ (f : ℤ → Fin (a+4)) (p : ℤ), x.tape stack = FiniteReturnStack.wordPart f p
      (FiniteReturnStack.address capacity (encoding pieces pc)) k le_rfl ∧
    x.head stack = p+k ∧ (∀ j < k, f (p+j) = blank) ∧ setTape x stack f p = y

/-- **The specification of the blocks** on the frames of the family, with cutoff `m`, `W` roles
and the ranks `rank` of the block calls. -/
structure Spec (m W : ℕ) (rank : Call → ℕ) where
  /-- The calls of the family. -/
  Frame : Type
  size : Frame → ℕ
  vol : Frame → ℕ
  ret : Frame → PC pieces.length
  entry : Frame → Tapes t a
  exit : Frame → Tapes t a
  /-- The leaf pairs: the remainder, or every pair below the cutoff. -/
  leaves : Frame → ℕ
  leafBank : Frame → ℕ → Tapes t a
  pieceBank : Frame → ℕ → Tapes t a
  done : Frame → Tapes t a
  finished : Frame → Tapes t a
  cPrepare : Frame → ℕ
  cTest : Frame → ℕ
  cLeaf : Frame → ℕ
  cSplit : Frame → ℕ
  cMerge : Frame → ℕ
  cFinish : Frame → ℕ
  cSeg : Frame → Seg → ℕ
  /-- The entry and recovery blocks of a call. -/
  cCall : Frame → Call → ℕ
  prepare : ∀ x, Runs impl.prepare (entry x) (leafBank x 0) (cPrepare x)
  test_leaf : ∀ x, ∀ i < leaves x, Tests impl (leafBank x i) .leaf (cTest x)
  test_end : ∀ x, Tests impl (leafBank x (leaves x)) (if m ≤ size x then .node else .done) (cTest x)
  leaf : ∀ x, ∀ i < leaves x, Runs impl.leaf (leafBank x i) (leafBank x (i+1)) (cLeaf x)
  split : ∀ x, m ≤ size x → Runs impl.split (leafBank x (leaves x)) (pieceBank x 0) (cSplit x)
  seg : ∀ x, m ≤ size x → ∀ (i : Site pieces) (s : Seg), pieces[i] = .seg s →
    Runs (impl.segment s) (pieceBank x i.val) (pieceBank x (i.val+1)) (cSeg x s)
  call : ∀ x, m ≤ size x → ∀ (i : Site pieces) (c : Call), pieces[i] = .call c →
    ∃ y, size y = rank c * (size x / m) ∧ (vol y : ℝ) = vol x / W ∧ ret y = .recover i ∧
      ∃ E R, E + R ≤ cCall x c ∧
        Runs (impl.enter c (returnCode pieces capacity i)) (pieceBank x i.val) (entry y) E ∧
        Runs (impl.recover c) (exit y) (pieceBank x (i.val+1)) R
  merge : ∀ x, m ≤ size x → Runs impl.merge (pieceBank x pieces.length) (done x) (cMerge x)
  done_leaf : ∀ x, ¬ m ≤ size x → done x = leafBank x (leaves x)
  finish : ∀ x, Runs impl.finish (done x) (finished x) (cFinish x)
  pop : ∀ x, Pops pieces capacity stack (finished x) (ret x) (exit x)

variable {pieces capacity stack ht impl} {m W : ℕ} {rank : Call → ℕ}
  (S : Spec pieces capacity stack impl m W rank)

/-- A frame's own cost: its blocks and edges, without its children. -/
def Spec.ownCost (x : S.Frame) : ℝ :=
  S.cPrepare x + 1 + S.leaves x * (S.cTest x + 1 + (S.cLeaf x + 1)) + (S.cTest x + 1) +
    (if m ≤ S.size x then S.cSplit x + 1 +
      (pieces.map (segCall (fun s => (S.cSeg x s : ℝ) + 1) fun c => (S.cCall x c : ℝ) + 2)).sum +
      (S.cMerge x + 1) else 0) +
    (S.cFinish x + 1) + (k + 2)

/-- **The contract**: every frame of `n` atoms runs from the graph's entry to its return address
within `B` of its volume. -/
def Contract (n : ℕ) (B : ℝ) : Prop :=
  ∀ x, S.size x = n → ∃ s : ℕ, (s : ℝ) ≤ B * S.vol x ∧
    run (program pieces capacity stack ht impl) s
      (entryConfig pieces capacity stack ht impl .prepare (S.entry x)) =
      some (entryConfig pieces capacity stack ht impl (S.ret x) (S.exit x))

theorem test_run (x : Tapes t a) (e : Exit) (B : ℕ) (h : Tests impl x e B) :
    ∃ n ≤ B+1, run (program pieces capacity stack ht impl) n
      (entryConfig pieces capacity stack ht impl .test x) =
      some (entryConfig pieces capacity stack ht impl (exitPC pieces e) x) := by
  obtain ⟨n, hn, st, he, hr, hh⟩ := h
  refine ⟨n+1, by omega, ?_⟩
  rw [← he]
  exact test_jump pieces capacity stack ht impl x n st hr hh

/-- **A frame's run.** If the children meet the contract at costs `T`, the frame runs within its
own cost and `Σ_r T(r⌊n/m⌋)/W` of its volume. -/
theorem frame_run (x : S.Frame) (T : ℕ → ℝ)
    (hc : m ≤ S.size x → ∀ r ∈ ranks rank pieces,
      Contract (ht := ht) S (r * (S.size x / m)) (T (r * (S.size x / m)))) :
    ∃ s : ℕ, (s : ℝ) ≤ S.ownCost x + (if m ≤ S.size x then
        ((ranks rank pieces).map fun r => T (r * (S.size x / m)) / W).sum * S.vol x else 0) ∧
      run (program pieces capacity stack ht impl) s
        (entryConfig pieces capacity stack ht impl .prepare (S.entry x)) =
        some (entryConfig pieces capacity stack ht impl (S.ret x) (S.exit x)) := by
  set P := program pieces capacity stack ht impl
  set E := entryConfig pieces capacity stack ht impl
  -- the preparation
  obtain ⟨n₁, hn₁, hr₁⟩ := block_jump pieces capacity stack ht impl .prepare .test _ _ _
    (S.prepare x) (fun _ => rfl)
  -- the leaf loop
  obtain ⟨n₂, hn₂, hr₂⟩ := chain (M := P) (fun i => E .test (S.leafBank x i))
    (fun _ => (S.cTest x + 1 + (S.cLeaf x + 1) : ℝ)) (S.leaves x) (fun i hi => by
      obtain ⟨a₁, ha₁, hra⟩ := test_run (ht := ht) (S.leafBank x i) .leaf _ (S.test_leaf x i hi)
      obtain ⟨a₂, ha₂, hrb⟩ := block_jump pieces capacity stack ht impl .leaf .test _ _ _
        (S.leaf x i hi) (fun _ => rfl)
      refine ⟨a₁ + a₂, ?_, join hra hrb⟩
      have h1 : (a₁ : ℝ) ≤ S.cTest x + 1 := by exact_mod_cast ha₁
      have h2 : (a₂ : ℝ) ≤ S.cLeaf x + 1 := by exact_mod_cast ha₂
      push_cast; linarith)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hn₂
  obtain ⟨n₃, hn₃, hr₃⟩ := test_run (ht := ht) _ _ _ (S.test_end x)
  -- the finish and the return
  obtain ⟨n₅, hn₅, hr₅⟩ := block_jump pieces capacity stack ht impl .finish .pop _ _ _
    (S.finish x) (fun _ => rfl)
  obtain ⟨f, p, hs, hh, hf, hy⟩ := S.pop x
  have hr₆ := pop_jump pieces capacity stack ht impl (S.ret x) _ f p hs hh hf
  rw [hy] at hr₆
  have hk : (0 : ℝ) ≤ S.leaves x := Nat.cast_nonneg _
  have c₁ : (n₁ : ℝ) ≤ S.cPrepare x + 1 := by exact_mod_cast hn₁
  have c₃ : (n₃ : ℝ) ≤ S.cTest x + 1 := by exact_mod_cast hn₃
  have c₅ : (n₅ : ℝ) ≤ S.cFinish x + 1 := by exact_mod_cast hn₅
  by_cases hm : m ≤ S.size x
  · -- the node
    simp only [hm, ite_true] at hr₃ ⊢
    obtain ⟨nsp, hnsp, hrsp⟩ := block_jump pieces capacity stack ht impl .split (first pieces) _ _ _
      (S.split x hm) (fun _ => rfl)
    set g : ℕ → ℝ := fun r => T (r * (S.size x / m)) / W * S.vol x
    obtain ⟨nsc, hnsc, hrsc⟩ := schedule_run pieces capacity stack ht impl (S.pieceBank x)
      (segCall (fun s => (S.cSeg x s : ℝ) + 1) fun c => (S.cCall x c : ℝ) + 2 + g (rank c)) (fun i => by
      generalize hp : pieces[i] = piece
      cases piece with
      | seg s =>
        obtain ⟨n, hn, hr⟩ := seg_jump pieces capacity stack ht impl i s hp _ _ _ (S.seg x hm i s hp)
        refine ⟨n, ?_, hr⟩
        simp only [segCall]
        exact_mod_cast hn
      | call c =>
        obtain ⟨y, hsize, hvol, hret, E', R, hER, he, hrr⟩ := S.call x hm i c hp
        obtain ⟨n, hn, hr⟩ := hc hm (rank c) (rank_mem rank pieces i.val i.isLt c hp) y hsize
        rw [hret] at hr
        obtain ⟨n', hn', hr'⟩ := call_jump pieces capacity stack ht impl i c hp _ _ _ _ E' R _ he
          ⟨n, hn, hr⟩ hrr
        refine ⟨n', ?_, hr'⟩
        simp only [segCall]
        have hER' : (E' : ℝ) + R ≤ S.cCall x c := by exact_mod_cast hER
        have hgy : T (rank c * (S.size x / m)) * S.vol y = g (rank c) := by
          simp only [g, hvol]; ring
        rw [hgy] at hn'
        linarith)
    obtain ⟨nm, hnm, hrm⟩ := block_jump pieces capacity stack ht impl .merge .finish _ _ _
      (S.merge x hm) (fun _ => rfl)
    have hsum := sum_calls rank g (fun s => (S.cSeg x s : ℝ) + 1) (fun c => (S.cCall x c : ℝ) + 2) pieces
    rw [hsum] at hnsc
    have hg : ((ranks rank pieces).map g).sum =
        ((ranks rank pieces).map fun r => T (r * (S.size x / m)) / W).sum * S.vol x := by
      rw [List.sum_map_mul_right]
    refine ⟨n₁ + n₂ + n₃ + nsp + nsc + nm + n₅ + (k+2), ?_,
      join (join (join (join (join (join (join hr₁ hr₂) hr₃) hrsp) hrsc) hrm) hr₅) hr₆⟩
    have csp : (nsp : ℝ) ≤ S.cSplit x + 1 := by exact_mod_cast hnsp
    have cm : (nm : ℝ) ≤ S.cMerge x + 1 := by exact_mod_cast hnm
    simp only [Spec.ownCost, hm, ite_true]
    push_cast
    rw [← hg]
    linarith
  · simp only [hm, ite_false] at hr₃ ⊢
    rw [S.done_leaf x hm] at hr₅
    refine ⟨n₁ + n₂ + n₃ + n₅ + (k+2), ?_, join (join (join (join hr₁ hr₂) hr₃) hr₅) hr₆⟩
    simp only [Spec.ownCost, hm, ite_false]
    push_cast
    linarith

/-- **The family's contract on the graph.** With the moment gaps of the ranks and the frames' own
work at most `C L` of the volume below the cutoff and `C n + C L` above it, every frame of `n ≥ 1`
atoms runs within `C/(1-q₁) n + C/(1-q_τ) n^τ L` of its volume. -/
theorem contract (hm : 2 ≤ m) (hW : 0 < W)
    (hpos : ∀ r ∈ ranks rank pieces, 1 ≤ r) (hle : ∀ r ∈ ranks rank pieces, r < m)
    {τ q₁ qτ C L : ℝ} (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hq₁ : q₁ < 1) (hqτ0 : 0 ≤ qτ) (hqτ : qτ < 1)
    (hmom₁ : ((ranks rank pieces).map fun r : ℕ => (1 / (W : ℝ)) * ((r : ℝ) / m)).sum ≤ q₁)
    (hmomτ : ((ranks rank pieces).map fun r : ℕ => (1 / (W : ℝ)) * ((r : ℝ) / m) ^ τ).sum ≤ qτ)
    (hleaf : ∀ x, S.size x < m → S.ownCost x ≤ C * L * S.vol x)
    (hnode : ∀ x, m ≤ S.size x → S.ownCost x ≤ (C * S.size x + C * L) * S.vol x) :
    ∀ n, 1 ≤ n → Contract (ht := ht) S n (C / (1 - q₁) * n + C / (1 - qτ) * ((n : ℝ) ^ τ * L)) := by
  refine family_contract (Contract (ht := ht) S) ?_ m W hm hW (ranks rank pieces) hpos hle hτ hC hL
    hq₁ hqτ0 hqτ hmom₁ hmomτ ?_ ?_
  · intro n B B' h hB x hx
    obtain ⟨s, hs, hr⟩ := h x hx
    exact ⟨s, hs.trans (mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg _)), hr⟩
  · intro n _ hn x hx
    obtain ⟨s, hs, hr⟩ := frame_run (ht := ht) S x (fun _ => 0) (fun h => absurd h (by omega))
    have hlt : ¬ m ≤ S.size x := by omega
    simp only [hlt, ite_false, add_zero] at hs
    exact ⟨s, hs.trans (hleaf x (by omega)), hr⟩
  · intro n hn T hT x hx
    subst hx
    obtain ⟨s, hs, hr⟩ := frame_run (ht := ht) S x T (fun _ => hT)
    simp only [hn, ite_true] at hs
    refine ⟨s, ?_, hr⟩
    have := hnode x hn
    nlinarith

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphContract
