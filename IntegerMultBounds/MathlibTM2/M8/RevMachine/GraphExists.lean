module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphContract

/-!
# The contract of the control graph from block invariants

`GraphContract` closes the family's recursion from a specification that names every bank of
every frame. The blocks determine those banks, so it is enough to know, block by block, that
from every bank of the right shape the block runs to some bank of the next shape (`Inv`): the
shapes are predicates on banks, indexed by the frame's parameters and its entry bank. A frame
ends at some bank of its exit shape; at a call, the child's exit shape is all the recovery block
needs.

`frame_run` and `contract` are `GraphContract.frame_run` and `GraphContract.contract` in this
form: every frame of `n ≥ 1` atoms runs from its entry bank to some bank of its exit shape at
its return address within `C/(1-q₁) n + C/(1-q_τ) n^τ L` of its volume.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists

noncomputable section
open IntegerMultBounds.Machine
open Graph GraphRun
open GraphContract (Runs Tests Pops segCall ranks rank_mem sum_calls test_run)
open SharedBankStageInput (raw)

/-- Runs that chain through banks of given shapes. -/
theorem chain {β : Type} {t q a : ℕ} {M : Program t q a} (cfg : ℕ → β → Config t q a)
    (P : ℕ → β → Prop) (bound : ℕ → ℝ) (y₀ : β) (h₀ : P 0 y₀) :
    ∀ N, (∀ i < N, ∀ y, P i y → ∃ y', P (i+1) y' ∧ ∃ s : ℕ, (s : ℝ) ≤ bound i ∧
      run M s (cfg i y) = some (cfg (i+1) y')) →
      ∃ y, P N y ∧ ∃ s : ℕ, (s : ℝ) ≤ ∑ i ∈ Finset.range N, bound i ∧ run M s (cfg 0 y₀) = some (cfg N y)
  | 0, _ => ⟨y₀, h₀, 0, by simp, rfl⟩
  | N+1, h => by
    obtain ⟨y, hy, s, hs, hr⟩ := chain cfg P bound y₀ h₀ N fun i hi => h i (by omega)
    obtain ⟨y', hy', s', hs', hr'⟩ := h N (by omega) y hy
    refine ⟨y', hy', s + s', ?_, ?_⟩
    · rw [Finset.sum_range_succ]; push_cast; linarith
    · rw [run_add, hr, Option.bind_some, hr']

variable {Seg Call : Type} {t a k : ℕ} (pieces : List (Piece Seg Call))
  (capacity : Fintype.card (PC pieces.length) ≤ 2^k) (stack : Fin t) (ht : 0 < t)
  (impl : Implementation t a k Seg Call)

/-- **The block invariants** of the family, with cutoff `m`, `W` roles and the ranks `rank` of
the block calls. A frame has parameters `σ : Shape` and an entry bank `x₀`; the other shapes
are predicates on banks given `σ` and `x₀`. -/
structure Inv (m W : ℕ) (rank : Call → ℕ) where
  Shape : Type
  size : Shape → ℕ
  vol : Shape → ℕ
  ret : Shape → PC pieces.length
  leaves : Shape → ℕ
  Entry : Shape → Tapes t a → Prop
  Leaf : Shape → Tapes t a → ℕ → Tapes t a → Prop
  Node : Shape → Tapes t a → ℕ → Tapes t a → Prop
  Done : Shape → Tapes t a → Tapes t a → Prop
  Finished : Shape → Tapes t a → Tapes t a → Prop
  Exit : Shape → Tapes t a → Tapes t a → Prop
  cPrepare : Shape → ℕ
  cTest : Shape → ℕ
  cLeaf : Shape → ℕ
  cSplit : Shape → ℕ
  cMerge : Shape → ℕ
  cFinish : Shape → ℕ
  cSeg : Shape → Seg → ℕ
  cCall : Shape → Call → ℕ
  prepare : ∀ σ x₀, Entry σ x₀ → ∃ y, Leaf σ x₀ 0 y ∧ Runs impl.prepare x₀ y (cPrepare σ)
  test_leaf : ∀ σ x₀ i y, Entry σ x₀ → i < leaves σ → Leaf σ x₀ i y → Tests impl y .leaf (cTest σ)
  test_end : ∀ σ x₀ y, Entry σ x₀ → Leaf σ x₀ (leaves σ) y →
    Tests impl y (if m ≤ size σ then .node else .done) (cTest σ)
  leaf : ∀ σ x₀ i y, Entry σ x₀ → i < leaves σ → Leaf σ x₀ i y →
    ∃ y', Leaf σ x₀ (i+1) y' ∧ Runs impl.leaf y y' (cLeaf σ)
  split : ∀ σ x₀ y, Entry σ x₀ → m ≤ size σ → Leaf σ x₀ (leaves σ) y →
    ∃ y', Node σ x₀ 0 y' ∧ Runs impl.split y y' (cSplit σ)
  seg : ∀ σ x₀ y, Entry σ x₀ → m ≤ size σ → ∀ (i : Site pieces) (s : Seg), pieces[i] = .seg s →
    Node σ x₀ i.val y → ∃ y', Node σ x₀ (i.val+1) y' ∧ Runs (impl.segment s) y y' (cSeg σ s)
  call : ∀ σ x₀ y, Entry σ x₀ → m ≤ size σ → ∀ (i : Site pieces) (c : Call), pieces[i] = .call c →
    Node σ x₀ i.val y → ∃ τ y₁, size τ = rank c * (size σ / m) ∧ (vol τ : ℝ) = vol σ / W ∧
      ret τ = .recover i ∧ Entry τ y₁ ∧ ∃ E R, E + R ≤ cCall σ c ∧
        Runs (impl.enter c (returnCode pieces capacity i)) y y₁ E ∧
        ∀ z, Exit τ y₁ z → ∃ y', Node σ x₀ (i.val+1) y' ∧ Runs (impl.recover c) z y' R
  merge : ∀ σ x₀ y, Entry σ x₀ → m ≤ size σ → Node σ x₀ pieces.length y →
    ∃ y', Done σ x₀ y' ∧ Runs impl.merge y y' (cMerge σ)
  done_leaf : ∀ σ x₀ y, Entry σ x₀ → ¬ m ≤ size σ → Leaf σ x₀ (leaves σ) y → Done σ x₀ y
  finish : ∀ σ x₀ y, Entry σ x₀ → Done σ x₀ y → ∃ y', Finished σ x₀ y' ∧ Runs impl.finish y y' (cFinish σ)
  pop : ∀ σ x₀ y, Entry σ x₀ → Finished σ x₀ y → ∃ z, Exit σ x₀ z ∧ Pops pieces capacity stack y (ret σ) z

variable {pieces capacity stack ht impl} {m W : ℕ} {rank : Call → ℕ}
  (S : Inv pieces capacity stack impl m W rank)

/-- A frame's own cost: its blocks and edges, without its children. -/
def Inv.ownCost (σ : S.Shape) : ℝ :=
  S.cPrepare σ + 1 + S.leaves σ * (S.cTest σ + 1 + (S.cLeaf σ + 1)) + (S.cTest σ + 1) +
    (if m ≤ S.size σ then S.cSplit σ + 1 +
      (pieces.map (segCall (fun s => (S.cSeg σ s : ℝ) + 1) fun c => (S.cCall σ c : ℝ) + 2)).sum +
      (S.cMerge σ + 1) else 0) +
    (S.cFinish σ + 1) + (k + 2)

/-- **The contract**: every frame of `n` atoms runs from its entry bank to some bank of its exit
shape at its return address, within `B` of its volume. -/
def Contract (n : ℕ) (B : ℝ) : Prop :=
  ∀ σ x₀, S.size σ = n → S.Entry σ x₀ → ∃ z, S.Exit σ x₀ z ∧ ∃ s : ℕ, (s : ℝ) ≤ B * S.vol σ ∧
    run (program pieces capacity stack ht impl) s
      (entryConfig pieces capacity stack ht impl .prepare x₀) =
      some (entryConfig pieces capacity stack ht impl (S.ret σ) z)

variable (σ : S.Shape) (x₀ : Tapes t a) (hx : S.Entry σ x₀)
include hx

/-- The preparation, the leaf loop and the final test. -/
theorem leaves_run :
    ∃ yl, S.Leaf σ x₀ (S.leaves σ) yl ∧ ∃ s : ℕ,
      (s : ℝ) ≤ S.cPrepare σ + 1 + S.leaves σ * (S.cTest σ + 1 + (S.cLeaf σ + 1)) + (S.cTest σ + 1) ∧
      run (program pieces capacity stack ht impl) s
        (entryConfig pieces capacity stack ht impl .prepare x₀) =
        some (entryConfig pieces capacity stack ht impl
          (exitPC pieces (if m ≤ S.size σ then .node else .done)) yl) := by
  set P := program pieces capacity stack ht impl
  set E := entryConfig pieces capacity stack ht impl
  obtain ⟨y₀, hy₀, hp⟩ := S.prepare σ x₀ hx
  obtain ⟨n₁, hn₁, hr₁⟩ := block_jump pieces capacity stack ht impl .prepare .test _ _ _ hp (fun _ => rfl)
  obtain ⟨yl, hyl, n₂, hn₂, hr₂⟩ := chain (M := P)
    (fun _ y => E .test y) (S.Leaf σ x₀)
    (fun _ => (S.cTest σ + 1 + (S.cLeaf σ + 1) : ℝ)) y₀ hy₀ (S.leaves σ) (fun i hi y hy => by
      obtain ⟨a₁, ha₁, hra⟩ := test_run (ht := ht) y .leaf _ (S.test_leaf σ x₀ i y hx hi hy)
      obtain ⟨y', hy', hl⟩ := S.leaf σ x₀ i y hx hi hy
      obtain ⟨a₂, ha₂, hrb⟩ := block_jump pieces capacity stack ht impl .leaf .test _ _ _ hl (fun _ => rfl)
      refine ⟨y', hy', a₁ + a₂, ?_, join hra hrb⟩
      have h1 : (a₁ : ℝ) ≤ S.cTest σ + 1 := by exact_mod_cast ha₁
      have h2 : (a₂ : ℝ) ≤ S.cLeaf σ + 1 := by exact_mod_cast ha₂
      push_cast; linarith)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hn₂
  obtain ⟨n₃, hn₃, hr₃⟩ := test_run (ht := ht) _ _ _ (S.test_end σ x₀ yl hx hyl)
  refine ⟨yl, hyl, n₁ + n₂ + n₃, ?_, join (join hr₁ hr₂) hr₃⟩
  have c₁ : (n₁ : ℝ) ≤ S.cPrepare σ + 1 := by exact_mod_cast hn₁
  have c₃ : (n₃ : ℝ) ≤ S.cTest σ + 1 := by exact_mod_cast hn₃
  push_cast; linarith

/-- The finish and the return, from any done bank. -/
theorem tail_run (yd : Tapes t a) (hyd : S.Done σ x₀ yd) :
    ∃ z, S.Exit σ x₀ z ∧ ∃ s : ℕ, (s : ℝ) ≤ S.cFinish σ + 1 + (k + 2) ∧
      run (program pieces capacity stack ht impl) s (entryConfig pieces capacity stack ht impl .finish yd) =
        some (entryConfig pieces capacity stack ht impl (S.ret σ) z) := by
  obtain ⟨yf, hyf, hfin⟩ := S.finish σ x₀ yd hx hyd
  obtain ⟨n₅, hn₅, hr₅⟩ := block_jump pieces capacity stack ht impl .finish .pop _ _ _ hfin (fun _ => rfl)
  obtain ⟨z, hz, f, p, hs, hh, hf, hy⟩ := S.pop σ x₀ yf hx hyf
  have hr₆ := pop_jump pieces capacity stack ht impl (S.ret σ) _ f p hs hh hf
  rw [hy] at hr₆
  refine ⟨z, hz, n₅ + (k+2), ?_, join hr₅ hr₆⟩
  have c₅ : (n₅ : ℝ) ≤ S.cFinish σ + 1 := by exact_mod_cast hn₅
  push_cast; linarith

/-- One piece of the schedule. -/
theorem piece_run (hm : m ≤ S.size σ) (T : ℕ → ℝ)
    (hc : ∀ r ∈ ranks rank pieces, Contract (ht := ht) S (r * (S.size σ / m)) (T (r * (S.size σ / m))))
    (i : Site pieces) (y : Tapes t a) (hy : S.Node σ x₀ i.val y) :
    ∃ y', S.Node σ x₀ (i.val+1) y' ∧ ∃ s : ℕ, (s : ℝ) ≤ segCall (fun s => (S.cSeg σ s : ℝ) + 1)
        (fun c => (S.cCall σ c : ℝ) + 2 + T (rank c * (S.size σ / m)) / W * S.vol σ) pieces[i] ∧
      run (program pieces capacity stack ht impl) s (entryConfig pieces capacity stack ht impl (.piece i) y) =
        some (entryConfig pieces capacity stack ht impl (successor pieces i) y') := by
  generalize hpc : pieces[i] = piece
  cases piece with
  | seg s =>
    obtain ⟨y', hy', hb⟩ := S.seg σ x₀ y hx hm i s hpc hy
    obtain ⟨n, hn, hr⟩ := seg_jump pieces capacity stack ht impl i s hpc _ _ _ hb
    exact ⟨y', hy', n, by simp only [segCall]; exact_mod_cast hn, hr⟩
  | call c =>
    obtain ⟨τ, y₁, hsize, hvol, hret, hy₁, E', R, hER, he, hrec⟩ := S.call σ x₀ y hx hm i c hpc hy
    obtain ⟨z, hz, n, hn, hr⟩ := hc (rank c) (rank_mem rank pieces i.val i.isLt c hpc) τ y₁ hsize hy₁
    obtain ⟨y', hy', hb⟩ := hrec z hz
    rw [hret] at hr
    obtain ⟨n', hn', hr'⟩ := call_jump pieces capacity stack ht impl i c hpc _ _ _ _ E' R _ he
      ⟨n, hn, hr⟩ hb
    refine ⟨y', hy', n', ?_, hr'⟩
    simp only [segCall]
    have hER' : (E' : ℝ) + R ≤ S.cCall σ c := by exact_mod_cast hER
    have hgy : T (rank c * (S.size σ / m)) * S.vol τ = T (rank c * (S.size σ / m)) / W * S.vol σ := by
      rw [hvol]; ring
    rw [hgy] at hn'
    linarith

/-- The node's schedule. -/
theorem schedule_run (hm : m ≤ S.size σ) (T : ℕ → ℝ)
    (hc : ∀ r ∈ ranks rank pieces, Contract (ht := ht) S (r * (S.size σ / m)) (T (r * (S.size σ / m))))
    (yn : Tapes t a) (hyn : S.Node σ x₀ 0 yn) :
    ∃ ym, S.Node σ x₀ pieces.length ym ∧ ∃ s : ℕ, (s : ℝ) ≤ (pieces.map (segCall (fun s => (S.cSeg σ s : ℝ) + 1)
        (fun c => (S.cCall σ c : ℝ) + 2 + T (rank c * (S.size σ / m)) / W * S.vol σ))).sum ∧
      run (program pieces capacity stack ht impl) s (entryConfig pieces capacity stack ht impl (first pieces) yn) =
        some (entryConfig pieces capacity stack ht impl .merge ym) := by
  set bound := segCall (fun s => (S.cSeg σ s : ℝ) + 1)
    (fun c => (S.cCall σ c : ℝ) + 2 + T (rank c * (S.size σ / m)) / W * S.vol σ)
  set P := program pieces capacity stack ht impl
  set E := entryConfig pieces capacity stack ht impl
  obtain ⟨ym, hym, nsc, hnsc, hrsc⟩ := chain (M := P)
    (fun i y => E (position pieces i) y) (S.Node σ x₀)
    (fun i => if hi : i < pieces.length then bound pieces[i] else 0) yn hyn pieces.length
    (fun i hi y hy => by
      have hp : position pieces i = .piece ⟨i, hi⟩ := by simp [position, hi]
      have hs : successor pieces ⟨i, hi⟩ = position pieces (i+1) := rfl
      obtain ⟨y', hy', n, hn, hr⟩ := piece_run (ht := ht) S σ x₀ hx hm T hc ⟨i, hi⟩ y hy
      refine ⟨y', hy', n, ?_, ?_⟩
      · simp only [hi, dite_true]; exact hn
      · rw [hp, ← hs]; exact hr)
  have hsum0 : ∑ i ∈ Finset.range pieces.length, (if hi : i < pieces.length then bound pieces[i] else 0) =
      (pieces.map bound).sum := by
    rw [Finset.sum_range, ← List.sum_ofFn]
    congr 1
    apply List.ext_get <;> simp
  rw [hsum0] at hnsc
  have hfirst : position pieces 0 = first pieces := by
    unfold position first; split_ifs <;> rfl
  have hlast : position pieces pieces.length = .merge := by simp [position]
  rw [hfirst, hlast] at hrsc
  exact ⟨ym, hym, nsc, hnsc, hrsc⟩

/-- **A frame's run.** -/
theorem frame_run (T : ℕ → ℝ)
    (hc : m ≤ S.size σ → ∀ r ∈ ranks rank pieces,
      Contract (ht := ht) S (r * (S.size σ / m)) (T (r * (S.size σ / m)))) :
    ∃ z, S.Exit σ x₀ z ∧ ∃ s : ℕ, (s : ℝ) ≤ S.ownCost σ + (if m ≤ S.size σ then
        ((ranks rank pieces).map fun r => T (r * (S.size σ / m)) / W).sum * S.vol σ else 0) ∧
      run (program pieces capacity stack ht impl) s
        (entryConfig pieces capacity stack ht impl .prepare x₀) =
        some (entryConfig pieces capacity stack ht impl (S.ret σ) z) := by
  obtain ⟨yl, hyl, n₁, hn₁, hr₁⟩ := leaves_run (ht := ht) S σ x₀ hx
  by_cases hm : m ≤ S.size σ
  · simp only [hm, ite_true] at hr₁ ⊢
    obtain ⟨yn, hyn, hsp⟩ := S.split σ x₀ yl hx hm hyl
    obtain ⟨nsp, hnsp, hrsp⟩ := block_jump pieces capacity stack ht impl .split (first pieces) _ _ _
      hsp (fun _ => rfl)
    obtain ⟨ym, hym, nsc, hnsc, hrsc⟩ := schedule_run (ht := ht) S σ x₀ hx hm T (hc hm) yn hyn
    obtain ⟨yd, hyd, hmg⟩ := S.merge σ x₀ ym hx hm hym
    obtain ⟨nm, hnm, hrm⟩ := block_jump pieces capacity stack ht impl .merge .finish _ _ _ hmg (fun _ => rfl)
    obtain ⟨z, hz, nt, hnt, hrt⟩ := tail_run (ht := ht) S σ x₀ hx yd hyd
    have hsum := sum_calls rank (fun r => T (r * (S.size σ / m)) / W * S.vol σ)
      (fun s => (S.cSeg σ s : ℝ) + 1) (fun c => (S.cCall σ c : ℝ) + 2) pieces
    rw [hsum, List.sum_map_mul_right] at hnsc
    refine ⟨z, hz, n₁ + nsp + nsc + nm + nt, ?_, join (join (join (join hr₁ hrsp) hrsc) hrm) hrt⟩
    have csp : (nsp : ℝ) ≤ S.cSplit σ + 1 := by exact_mod_cast hnsp
    have cm : (nm : ℝ) ≤ S.cMerge σ + 1 := by exact_mod_cast hnm
    unfold Inv.ownCost
    simp only [hm, ↓reduceIte]
    push_cast
    linarith
  · simp only [hm, ite_false] at hr₁ ⊢
    obtain ⟨z, hz, nt, hnt, hrt⟩ := tail_run (ht := ht) S σ x₀ hx yl (S.done_leaf σ x₀ yl hx hm hyl)
    refine ⟨z, hz, n₁ + nt, ?_, join hr₁ hrt⟩
    unfold Inv.ownCost
    simp only [hm, ↓reduceIte]
    push_cast
    linarith

omit hx

/-- **The family's contract on the graph**, from the block invariants. -/
theorem contract (hm : 2 ≤ m) (hW : 0 < W)
    (hpos : ∀ r ∈ ranks rank pieces, 1 ≤ r) (hle : ∀ r ∈ ranks rank pieces, r < m)
    {τ q₁ qτ C L : ℝ} (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hq₁ : q₁ < 1) (hqτ0 : 0 ≤ qτ) (hqτ : qτ < 1)
    (hmom₁ : ((ranks rank pieces).map fun r : ℕ => (1 / (W : ℝ)) * ((r : ℝ) / m)).sum ≤ q₁)
    (hmomτ : ((ranks rank pieces).map fun r : ℕ => (1 / (W : ℝ)) * ((r : ℝ) / m) ^ τ).sum ≤ qτ)
    (hleaf : ∀ σ x₀, S.Entry σ x₀ → S.size σ < m → S.ownCost σ ≤ C * L * S.vol σ)
    (hnode : ∀ σ x₀, S.Entry σ x₀ → m ≤ S.size σ → S.ownCost σ ≤ (C * S.size σ + C * L) * S.vol σ) :
    ∀ n, 1 ≤ n → Contract (ht := ht) S n (C / (1 - q₁) * n + C / (1 - qτ) * ((n : ℝ) ^ τ * L)) := by
  refine family_contract (Contract (ht := ht) S) ?_ m W hm hW (ranks rank pieces) hpos hle hτ hC hL
    hq₁ hqτ0 hqτ hmom₁ hmomτ ?_ ?_
  · intro n B B' h hB σ x₀ hσ hx
    obtain ⟨z, hz, s, hs, hr⟩ := h σ x₀ hσ hx
    exact ⟨z, hz, s, hs.trans (mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg _)), hr⟩
  · intro n _ hn σ x₀ hσ hx
    obtain ⟨z, hz, s, hs, hr⟩ := frame_run (ht := ht) S σ x₀ hx (fun _ => 0) (fun h => absurd h (by omega))
    have hlt : ¬ m ≤ S.size σ := by omega
    simp only [hlt, ite_false, add_zero] at hs
    exact ⟨z, hz, s, hs.trans (hleaf σ x₀ hx (by omega)), hr⟩
  · intro n hn T hT σ x₀ hσ hx
    subst hσ
    obtain ⟨z, hz, s, hs, hr⟩ := frame_run (ht := ht) S σ x₀ hx T (fun _ => hT)
    simp only [hn, ite_true] at hs
    refine ⟨z, hz, s, ?_, hr⟩
    have := hnode σ x₀ hx hn
    nlinarith

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
