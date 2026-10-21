module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Graph
public import IntegerMultBounds.Machine.SharedBankFamilyExact
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Runs on the control graph

A clean block contract lifts to a run of the graph from the block's entry to the entry of its
successor, one transition more for the edge (`block_jump`). The test keeps the bank and selects
its exit by its terminal state (`test_jump`); the pop erases the return code and reaches the
decoded block (`pop_jump`). A block call runs its entry block, the child's whole run from the
graph's entry to the call's recovery block, and the recovery block (`call_jump`). Runs chain
(`chain`), so the node's schedule runs piece after piece from its first block to the merge
(`schedule_run`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun

noncomputable section
open IntegerMultBounds.Machine
open Graph
open SharedBankStageInput (raw)
open SharedBankFamilyExact (atState)
open SharedPlacementAlphabet (setTape)

/-- Runs chain, and their real bounds add. -/
theorem chain {t q a : ℕ} {M : Program t q a} (cfg : ℕ → Config t q a) (bound : ℕ → ℝ) :
    ∀ N, (∀ i < N, ∃ s : ℕ, (s : ℝ) ≤ bound i ∧ run M s (cfg i) = some (cfg (i+1))) →
      ∃ s : ℕ, (s : ℝ) ≤ ∑ i ∈ Finset.range N, bound i ∧ run M s (cfg 0) = some (cfg N)
  | 0, _ => ⟨0, by simp, rfl⟩
  | N+1, h => by
    obtain ⟨s, hs, hr⟩ := chain cfg bound N fun i hi => h i (by omega)
    obtain ⟨s', hs', hr'⟩ := h N (by omega)
    refine ⟨s + s', ?_, ?_⟩
    · rw [Finset.sum_range_succ]; push_cast; linarith
    · rw [run_add, hr, Option.bind_some, hr']

theorem join {t q a n₁ n₂ : ℕ} {M : Program t q a} {c₁ c₂ c₃ : Config t q a}
    (h₁ : run M n₁ c₁ = some c₂) (h₂ : run M n₂ c₂ = some c₃) : run M (n₁+n₂) c₁ = some c₃ := by
  rw [run_add, h₁, Option.bind_some, h₂]

variable {Seg Call : Type} {t a k : ℕ} (pieces : List (Piece Seg Call))
  (capacity : Fintype.card (PC pieces.length) ≤ 2^k) (stack : Fin t) (ht : 0 < t)
  (impl : Implementation t a k Seg Call)

private theorem raw_self (v : Tapes t a) : raw v t = v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [dite_eq_left i.isLt]

/-- A padded member of the family and its edge. -/
theorem member_jump (i j : Fin (Fintype.card (PC pieces.length))) (before after : Tapes t a) (B : ℕ)
    (h : HoareTime (family pieces capacity stack ht impl i)
      (fun w => w = raw before (tapeCount pieces capacity stack ht impl))
      (fun w => w = raw after (tapeCount pieces capacity stack ht impl)) B)
    (he : ∀ st, next pieces capacity stack ht impl i st = some j) :
    ∃ steps ≤ B+1, run (program pieces capacity stack ht impl) steps
      (((raw before (tapeCount pieces capacity stack ht impl)).start
        (family pieces capacity stack ht impl i)).mapState
          (FiniteFlow.embed (states pieces capacity stack ht impl) i)) =
      some (((raw after (tapeCount pieces capacity stack ht impl)).start
        (family pieces capacity stack ht impl j)).mapState
          (FiniteFlow.embed (states pieces capacity stack ht impl) j)) := by
  obtain ⟨n, c, hn, hr, hhalt, hbank⟩ := h _ rfl
  have hj := FiniteFlow.block_then_jump (family pieces capacity stack ht impl)
    (next pieces capacity stack ht impl) (encoding pieces .prepare) i j _ n c hr hhalt (he c.state)
  rw [hbank] at hj
  exact ⟨n+1, by omega, hj⟩

/-- **A block and its edge.** -/
theorem block_jump (pc target : PC pieces.length) (before after : Tapes t a) (B : ℕ)
    (h : HoareTime (block pieces capacity stack ht impl pc).program
      (fun w => w = raw before (block pieces capacity stack ht impl pc).tapes)
      (fun w => w = raw after (block pieces capacity stack ht impl pc).tapes) B)
    (he : ∀ st, edge pieces capacity stack ht impl pc st = some target) :
    ∃ steps ≤ B+1, run (program pieces capacity stack ht impl) steps
      (entryConfig pieces capacity stack ht impl pc before) =
      some (entryConfig pieces capacity stack ht impl target after) := by
  have hpad := SharedBankFamily.realizes (block pieces capacity stack ht impl) pc before after B h
  have hi : (encoding pieces).symm (encoding pieces pc) = pc := (encoding pieces).symm_apply_apply _
  apply member_jump pieces capacity stack ht impl (encoding pieces pc) (encoding pieces target)
    before after B
  · unfold family states tapeCount
    rw [hi]
    exact hpad
  · unfold next states
    rw [hi]
    intro st
    rw [he st]
    rfl

/-- The test keeps the bank and ends in a terminal state that selects its exit. -/
theorem test_block (x : Tapes t a) (n : ℕ) (st : Fin impl.test.states)
    (hr : run impl.test.program n ((raw x impl.test.tapes).start impl.test.program) =
      some (atState (raw x impl.test.tapes) st))
    (hh : step impl.test.program (atState (raw x impl.test.tapes) st) = none) :
    ∃ c : Config (tapeCount pieces capacity stack ht impl)
      (states pieces capacity stack ht impl (encoding pieces .test)) a,
      run (family pieces capacity stack ht impl (encoding pieces .test)) n
        ((raw x (tapeCount pieces capacity stack ht impl)).start
          (family pieces capacity stack ht impl (encoding pieces .test))) = some c ∧
      step (family pieces capacity stack ht impl (encoding pieces .test)) c = none ∧
      c.tapes = raw x (tapeCount pieces capacity stack ht impl) ∧
      next pieces capacity stack ht impl (encoding pieces .test) c.state =
        some (encoding pieces (exitPC pieces (impl.exit st))) := by
  have hp := SharedBankFamilyExact.pad_exact impl.test.program
    (SharedBankFamily.block_le (block pieces capacity stack ht impl) .test)
    (SharedBankFamily.common_le impl.test) x x n st hr hh
  have he : (encoding pieces).symm (encoding pieces PC.test) = PC.test :=
    (encoding pieces).symm_apply_apply _
  unfold states family next tapeCount
  rw [he]
  exact ⟨atState (raw x _) st, hp.1, hp.2, rfl, rfl⟩

/-- **The test and its edge.** -/
theorem test_jump (x : Tapes t a) (n : ℕ) (st : Fin impl.test.states)
    (hr : run impl.test.program n ((raw x impl.test.tapes).start impl.test.program) =
      some (atState (raw x impl.test.tapes) st))
    (hh : step impl.test.program (atState (raw x impl.test.tapes) st) = none) :
    run (program pieces capacity stack ht impl) (n+1)
      (entryConfig pieces capacity stack ht impl .test x) =
      some (entryConfig pieces capacity stack ht impl (exitPC pieces (impl.exit st)) x) := by
  obtain ⟨c, hr', hhalt, hbank, hedge⟩ := test_block pieces capacity stack ht impl x n st hr hh
  have hj := FiniteFlow.block_then_jump (family pieces capacity stack ht impl)
    (next pieces capacity stack ht impl) (encoding pieces .prepare) (encoding pieces .test)
    _ _ n c hr' hhalt hedge
  rw [hbank] at hj
  exact hj

/-- The pop erases the return code and ends in the state of its return address. -/
theorem pop_block (pc : PC pieces.length) (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hs : v.tape stack = FiniteReturnStack.wordPart f p
      (FiniteReturnStack.address capacity (encoding pieces pc)) k le_rfl)
    (hh : v.head stack = p+k) (hf : ∀ j < k, f (p+j) = blank) :
    ∃ c : Config (tapeCount pieces capacity stack ht impl)
      (states pieces capacity stack ht impl (encoding pieces .pop)) a,
      run (family pieces capacity stack ht impl (encoding pieces .pop)) (k+1)
        ((raw v (tapeCount pieces capacity stack ht impl)).start
          (family pieces capacity stack ht impl (encoding pieces .pop))) = some c ∧
      step (family pieces capacity stack ht impl (encoding pieces .pop)) c = none ∧
      c.tapes = raw (setTape v stack f p) (tapeCount pieces capacity stack ht impl) ∧
      next pieces capacity stack ht impl (encoding pieces .pop) c.state = some (encoding pieces pc) := by
  let M := Placement.placed (FiniteReturnStack.pop a k) (FiniteReturnStackAt.placement stack)
  have hpop : run M (k+1) (v.start M) =
        some (atState (setTape v stack f p)
          (FiniteReturnStack.encode k (.inr (0, FiniteReturnStack.address capacity (encoding pieces pc))))) ∧
      step M (atState (setTape v stack f p)
          (FiniteReturnStack.encode k (.inr (0, FiniteReturnStack.address capacity (encoding pieces pc))))) =
        none := by
    obtain ⟨hr, hhalt⟩ := FiniteReturnStack.pop_exact (a := a)
      (FiniteReturnStack.address capacity (encoding pieces pc)) f p hf
    let e := FiniteReturnStackAt.placement stack
    let c := FiniteReturnStack.cfg (a := a)
      (.inr (0, FiniteReturnStack.address capacity (encoding pieces pc))) f p
    have hr' : run (FiniteReturnStack.pop a k) (k+1)
        ((Placement.active e v).start (FiniteReturnStack.pop a k)) = some c := by
      rw [FiniteReturnStackAt.active_bank, hs, hh]
      exact hr
    have he : Placement.result e v c = atState (setTape v stack f p)
        (FiniteReturnStack.encode k (.inr (0, FiniteReturnStack.address capacity (encoding pieces pc)))) := by
      have ht' : (Placement.result e v c).tapes = setTape v stack f p :=
        FiniteReturnStackAt.replace_bank stack v f p
      exact congrArg₂ (Config.mk _) (congrArg Tapes.head ht') (congrArg Tapes.tape ht')
    exact ⟨he ▸ Placement.placed_run _ e v hr', he ▸ Placement.placed_halt _ e v hhalt⟩
  have hp := SharedBankFamilyExact.pad_exact M
    (SharedBankFamily.block_le (block pieces capacity stack ht impl) .pop) (le_refl t)
    v (setTape v stack f p) (k+1) _ (by simpa only [raw_self] using hpop.1)
    (by simpa only [raw_self] using hpop.2)
  have he : (encoding pieces).symm (encoding pieces PC.pop) = PC.pop :=
    (encoding pieces).symm_apply_apply _
  unfold states family next tapeCount
  rw [he]
  refine ⟨atState (raw (setTape v stack f p) _) _, hp.1, hp.2, rfl, ?_⟩
  simp only [atState]
  rw [pop_edge]
  rfl

/-- **The pop and its edge**, to a call site's recovery block or to the root's halt. -/
theorem pop_jump (pc : PC pieces.length) (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hs : v.tape stack = FiniteReturnStack.wordPart f p
      (FiniteReturnStack.address capacity (encoding pieces pc)) k le_rfl)
    (hh : v.head stack = p+k) (hf : ∀ j < k, f (p+j) = blank) :
    run (program pieces capacity stack ht impl) (k+2)
      (entryConfig pieces capacity stack ht impl .pop v) =
      some (entryConfig pieces capacity stack ht impl pc (setTape v stack f p)) := by
  obtain ⟨c, hr, hhalt, hbank, hedge⟩ := pop_block pieces capacity stack ht impl pc v f p hs hh hf
  have hj := FiniteFlow.block_then_jump (family pieces capacity stack ht impl)
    (next pieces capacity stack ht impl) (encoding pieces .prepare) (encoding pieces .pop)
    (encoding pieces pc) _ (k+1) c hr hhalt hedge
  rw [hbank] at hj
  exact hj

/-- **A block call.** Its entry block, the child's run from the graph's entry to the recovery
block, and the recovery block. -/
theorem call_jump (i : Site pieces) (c : Call) (hi : pieces[i] = .call c)
    (before entered returned after : Tapes t a) (E R : ℕ) (Bc : ℝ)
    (he : HoareTime (impl.enter c (returnCode pieces capacity i)).program
      (fun w => w = raw before (impl.enter c (returnCode pieces capacity i)).tapes)
      (fun w => w = raw entered (impl.enter c (returnCode pieces capacity i)).tapes) E)
    (hc : ∃ n : ℕ, (n : ℝ) ≤ Bc ∧ run (program pieces capacity stack ht impl) n
      (entryConfig pieces capacity stack ht impl .prepare entered) =
        some (entryConfig pieces capacity stack ht impl (.recover i) returned))
    (hr : HoareTime (impl.recover c).program
      (fun w => w = raw returned (impl.recover c).tapes)
      (fun w => w = raw after (impl.recover c).tapes) R) :
    ∃ n : ℕ, (n : ℝ) ≤ E + 1 + Bc + (R + 1) ∧ run (program pieces capacity stack ht impl) n
      (entryConfig pieces capacity stack ht impl (.piece i) before) =
      some (entryConfig pieces capacity stack ht impl (successor pieces i) after) := by
  have hbe : block pieces capacity stack ht impl (.piece i) = impl.enter c (returnCode pieces capacity i) := by
    simp only [block, hi]
  have hbr : block pieces capacity stack ht impl (.recover i) = impl.recover c := by
    simp only [block, hi]
  obtain ⟨ne, hne, hte⟩ := block_jump pieces capacity stack ht impl (.piece i) .prepare before entered E
    (by rw [hbe]; exact he) (call_edge pieces capacity stack ht impl i c hi)
  obtain ⟨nc, hnc, htc⟩ := hc
  obtain ⟨nr, hnr, htr⟩ := block_jump pieces capacity stack ht impl (.recover i) (successor pieces i)
    returned after R (by rw [hbr]; exact hr) (recover_edge pieces capacity stack ht impl i)
  refine ⟨ne+nc+nr, ?_, join (join hte htc) htr⟩
  have h1 : (ne : ℝ) ≤ E + 1 := by exact_mod_cast hne
  have h2 : (nr : ℝ) ≤ R + 1 := by exact_mod_cast hnr
  push_cast
  linarith

/-- A nonrecursive piece of the schedule. -/
theorem seg_jump (i : Site pieces) (s : Seg) (hi : pieces[i] = .seg s)
    (before after : Tapes t a) (B : ℕ)
    (h : HoareTime (impl.segment s).program
      (fun w => w = raw before (impl.segment s).tapes)
      (fun w => w = raw after (impl.segment s).tapes) B) :
    ∃ n ≤ B+1, run (program pieces capacity stack ht impl) n
      (entryConfig pieces capacity stack ht impl (.piece i) before) =
      some (entryConfig pieces capacity stack ht impl (successor pieces i) after) := by
  have hb : block pieces capacity stack ht impl (.piece i) = impl.segment s := by
    simp only [block, hi]
  exact block_jump pieces capacity stack ht impl (.piece i) (successor pieces i) before after B
    (by rw [hb]; exact h) (seg_edge pieces capacity stack ht impl i s hi)

/-- The block before position `i` of the schedule: piece `i`, or the merge after the last. -/
def position (i : ℕ) : PC pieces.length := if h : i < pieces.length then .piece ⟨i, h⟩ else .merge

/-- **The schedule.** If every piece runs from its bank to the next, the schedule runs from its
first block to the merge, within the sum of the pieces' bounds. -/
theorem schedule_run (banks : ℕ → Tapes t a) (bound : Piece Seg Call → ℝ)
    (h : ∀ i : Site pieces, ∃ n : ℕ, (n : ℝ) ≤ bound pieces[i] ∧
      run (program pieces capacity stack ht impl) n
        (entryConfig pieces capacity stack ht impl (.piece i) (banks i.val)) =
        some (entryConfig pieces capacity stack ht impl (successor pieces i) (banks (i.val+1)))) :
    ∃ n : ℕ, (n : ℝ) ≤ (pieces.map bound).sum ∧ run (program pieces capacity stack ht impl) n
      (entryConfig pieces capacity stack ht impl (first pieces) (banks 0)) =
      some (entryConfig pieces capacity stack ht impl .merge (banks pieces.length)) := by
  have hc := chain (fun i => entryConfig pieces capacity stack ht impl (position pieces i) (banks i))
    (fun i => if hi : i < pieces.length then bound pieces[i] else 0) pieces.length (fun i hi => by
      obtain ⟨n, hn, hr⟩ := h ⟨i, hi⟩
      refine ⟨n, by simpa [hi] using hn, ?_⟩
      have hp : position pieces i = .piece ⟨i, hi⟩ := by simp [position, hi]
      have hs : successor pieces ⟨i, hi⟩ = position pieces (i+1) := rfl
      rw [hp]; rw [hs] at hr; exact hr)
  obtain ⟨n, hn, hr⟩ := hc
  have hsum : ∑ i ∈ Finset.range pieces.length, (if hi : i < pieces.length then bound pieces[i] else 0) =
      (pieces.map bound).sum := by
    rw [← Fin.sum_univ_fun_getElem pieces bound, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by simp [i.isLt]
  have h0 : position pieces 0 = first pieces := rfl
  have hl : position pieces pieces.length = .merge := by simp [position]
  refine ⟨n, hsum ▸ hn, ?_⟩
  rw [← h0, ← hl]
  exact hr

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
