module

public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap
public import IntegerMultBounds.MathlibTM2.Host.Placed
public import IntegerMultBounds.MathlibTM2.Host.Index
public import IntegerMultBounds.Schoenhage.SSClean

/-!
# Schönhage–Strassen multiplication as a host subroutine

`ssMul` multiplies two binary integers held on host registers by running the vendored
Schönhage–Strassen multiplier as a foreign machine.

**The machine.** `SS.cleanProgram` is the compiled word program `ssClean` (the multiplier
`ssMain` followed by a wipe of its registers), a literal 64-tape program over `Fin 4`.
`SS.clean_hoare` is its exact contract: from the bank `SS.startBank (topN m) a b` (the words
`rwd N a`, `rwd N b` on tape `tIn`, `ones N` on tape `pN`, every other tape empty) it halts within
`SS.cleanBound m` transitions on the bank `SS.doneBank (topN m) (a * b)` (the word
`rwd N (a * b)` alone on `tIn`). The host runs it through the alphabet encoding `SS.code A` of
`Fin 4` into `Fin (A + 4)` (every symbol keeps its code) and the state embedding `liftQ`
(`SS.machine`).

**Placed runs.** `placedRun M ι` runs a program placed on an injective family `ι` of host
registers: it marks every unplaced register, runs the placed program with `foreign`, normalizes
the placed registers and unmarks (the pattern of `placedSwapProg`). `placedRun_exec` turns an
exact contract between word-tape banks into an execution: the placed registers go from the cells
of the start bank to the cells of the final bank, every other stack is unchanged.

**Register interface of `ssMul ι … xa xb xn xc`.**
* `ι : Fin 64 → Fin T` (injective) holds the multiplier's tapes; these registers are empty
  (both stacks) before and after. `ι 0`, `ι 1`, `ι 2`, `ι 3` also serve as scratch registers
  for laying out the input, and `ι 0` for reading out the product.
* `xa`, `xb` hold the operands `a, b < 2 ^ m` as `binSyms m a`, `binSyms m b` (`m` bit symbols,
  least significant bit on top); they are restored. `xa = xb` is allowed.
* `xn` holds `topN m` symbols (the multiplier size `N` in unary, any symbols); it is restored.
* `xc` receives the product: `binSyms (topN m + 1) (a * b)` is pushed on top of its content.
  This is the vendored word `rwd N (a * b)` as bit symbols; its bits from `2 * m` on are zero
  (`SS.binSyms_product`).

`ssMul` lays out the start bank (`SS.layout`: the operands padded with zero bits to `N + 1` bits
by a counted copy `SS.padCopy` against `xn`, and `N` unary ones copied from `xn`), runs the placed
multiplier (`placedRun`), and moves the product word without its separator to `xc`
(`SS.readOut`).

`ssMul_exec`: exact result, `v'.user = v.user`, every other stack unchanged, within
`(T + 773) * ssCostBound m + 164 * m + 463` host steps, where `ssCostBound m` is the cleaned
multiplier's bound plus two. `ssMul_cost_le` bounds this by
`ssMulConst * (T + 1) * (m * (log m + 1) * (log log m + 1))` (`Nat.log 2`), and `ssMul_exec_log`
states the execution with that bound.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2


noncomputable section

namespace SS

open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule
  IntegerMultBounds.Schoenhage.Tp

/-- The cleaned multiplier compiled to a literal 64-tape program over the binary alphabet. -/
def cleanProgram : Program 64 (compile (a := 0) (by decide) ssClean).1 0 :=
  (compile (a := 0) (by decide) ssClean).2

/-- The start bank: the operands on `tIn`, `ones N` on `pN`, every other tape empty. -/
def startBank (N x y : ℕ) : Fin 64 → WTape :=
  Function.update (Function.update (fun _ => emp) tIn ⟨[], [rwd N x, rwd N y]⟩) pN
    (IntegerMultBounds.Schoenhage.reg (ones N))

/-- The final bank: the product alone on `tIn`. -/
def doneBank (N v : ℕ) : Fin 64 → WTape := Function.update (fun _ => emp) tIn ⟨[], [rwd N v]⟩

/-- The step bound of the cleaned multiplier on operands below `2 ^ m`. -/
def cleanBound (m : ℕ) : ℕ :=
  costC cA cB cC0 * (4 * m + 1) * (bitlen (4 * m) + 1) * (3 * bitlen (bitlen (4 * m)) + 1) +
    2480 * m + 55001

/-- The start bank meets the multiplier's precondition. -/
theorem startBank_start (N x y : ℕ) : SSStart N x y (startBank N x y) := by
  refine ⟨?_, by simp [startBank], fun i h1 h2 => ?_⟩
  · rw [startBank, Function.update_of_ne (by decide), Function.update_self]
  simp [startBank, Function.update_of_ne h1, Function.update_of_ne h2]

/-- The multiplier's final condition determines the bank. -/
theorem done_eq {N v : ℕ} {σ : Fin 64 → WTape} (h : SSDone N v σ) : σ = doneBank N v := by
  funext i
  by_cases hi : i = tIn
  · subst hi; simp [doneBank, h.1]
  · rw [doneBank, Function.update_of_ne hi, h.2 i hi]

/-- The cleaned multiplier as an exact contract: operands below `2 ^ m` at size `topN m`, the
exact product, within `cleanBound m` transitions. -/
theorem clean_hoare {m a b : ℕ} (hm : 1 ≤ m) (ha : a < 2 ^ m) (hb : b < 2 ^ m) :
    HoareTime cleanProgram (· = enc (startBank (topN m) a b)) (· = enc (doneBank (topN m) (a * b)))
      (cleanBound m) := by
  obtain ⟨hlt, hle, hk⟩ := topN_facts hm
  have hm2 : 2 ^ m ≤ 2 ^ topN m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hab : a * b < Fm (topN m) := by
    have : a * b < 2 ^ m * 2 ^ m := Nat.mul_lt_mul'' ha hb
    have h2 : 2 ^ m * 2 ^ m ≤ 2 ^ topN m := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold Fm; omega
  obtain ⟨σ', k, hx, hq, hkb⟩ := runs_ssClean (N := topN m) (by omega) hk (by unfold Fm; omega)
    (by unfold Fm; omega) _ (startBank_start (topN m) a b)
  rw [Nat.mod_eq_of_lt hab] at hq
  have hc := compile_correct (a := 0) (by decide) hx
  rw [done_eq hq] at hc
  refine hc.consequence (fun _ h => h) (fun _ h => h) ?_
  have h1 := ssCost_le (topN m) a b
  have h2 := cost_topN cA cB cC0 hm
  unfold cleanBound
  generalize costC cA cB cC0 * (4 * m + 1) * (bitlen (4 * m) + 1) *
    (3 * bitlen (bitlen (4 * m)) + 1) = X at *
  generalize cost cA cB cC0 (topN m) = Y at *
  generalize ssCost (topN m) [a, b] = Z at *
  clear hk hm2 hab ha hb hx hq hc
  generalize topN m = N at *
  linarith

end SS

/-! ### Running a placed word-tape program with an exact contract -/

section PlacedRun

open IntegerMultBounds.Schoenhage

variable {s T Q A : ℕ} {U F : Type}

/-- Run a program placed on host registers `ι`: mark every unplaced register, run, normalize
the placed registers, unmark. -/
def placedRun (M : Program s Q A) (ι : Fin s → Fin T) (hι : Function.Injective ι) (hT : s ≤ T) :
    Pr F T Q A U :=
  .seq (markList (unplaced ι))
    (.seq (foreign
        (Placement.placed M (InjectivePlacement.placement ι hι (Nat.add_sub_cancel' hT))))
      (.seq (normList (List.ofFn ι)) (dropList (unplaced ι))))

/-- Word cells are blank-free. -/
lemma SS.blank_not_mem_cells (ws : List (List Bool)) : (blank : Fin (A + 4)) ∉ cells ws := by
  intro h
  simp only [cells, List.mem_map] at h
  obtain ⟨o, -, ho⟩ := h
  exact sym_ne_blank o ho

/-- A word tape is the word tape of its cells. -/
lemma SS.wtape_eq_wordTape (σ : WTape) : σ.tape (a := A) = wordTape (cells σ.words) := rfl

/-- Running a placed program with an exact contract between word-tape banks. The placed
registers hold the start bank (heads at cell `0`), every left stack among them empty. Afterwards
the placed registers hold the cells of the final bank with empty left stacks, and every other
stack is unchanged. -/
theorem placedRun_exec (body : F → Pr F T Q A U) (M : Program s Q A) (ι : Fin s → Fin T)
    (hι : Function.Injective ι) (hT : s ≤ T) {σ₀ σ₁ : Fin s → WTape} {k : ℕ}
    (hM : HoareTime M (· = enc σ₀) (· = enc σ₁) k) (h0 : ∀ j, (σ₀ j).left = [])
    (v : HS T Q A U) (S : Stacks T A) (hL : ∀ j, S.L (ι j) = [])
    (hR : ∀ j, S.R (ι j) = cells (σ₀ j).right) :
    ∃ v' n R', v'.user = v.user ∧
      n ≤ (T + 12 * s + 5) * k + 6 * ∑ j, (S.R (ι j)).length + 2 * T + 6 * s + 9 ∧
      (∀ j, R' (ι j) = cells (σ₁ j).words) ∧ (∀ y, (∀ j, ι j ≠ y) → R' y = S.R y) ∧
      Exec body (placedRun M ι hι hT) (mk v S) n (mk v' { S with R := R' }) := by
  classical
  set pe := InjectivePlacement.placement ι hι (Nat.add_sub_cancel' hT) with hpe
  have hun : ∀ j, ι j ∉ unplaced ι := fun j hm => (mem_unplaced ι _).1 hm j rfl
  -- step 1: mark the unplaced registers
  have he₀ := markList_exec body (unplaced ι) (unplaced_nodup ι) v S
  set S₀ : Stacks T A :=
    { S with R := fun y => if y ∈ unplaced ι then blank :: S.R y else S.R y } with hS₀
  have hS₀ι : ∀ j, S₀.R (ι j) = S.R (ι j) := fun j => by simp [S₀, hun j]
  -- the host bank represented by `S₀`
  let w₀ : Tapes T A := ⟨fun _ => 0, fun y z => readAt blank (S₀.L y) (S₀.R y) z⟩
  let W := Placement.replace pe w₀ (enc σ₀)
  have hrep : RepT W S₀.L S₀.R := by
    intro y z
    by_cases hy : ∃ j, ι j = y
    · obtain ⟨j, rfl⟩ := hy
      rw [InjectivePlacement.replace_tape_slot, InjectivePlacement.replace_head_slot]
      show (σ₀ j).tape z = readAt blank (S.L (ι j)) (S₀.R (ι j)) (z - (σ₀ j).pos)
      rw [WTape.pos, h0 j, hL j, hS₀ι, hR j, clen_nil, Nat.cast_zero, sub_zero, readAt_nil_left,
        SS.wtape_eq_wordTape, WTape.words, h0 j, List.reverse_nil, List.nil_append]
    · have hy' : ∀ j, ι j ≠ y := fun j hj => hy ⟨j, hj⟩
      rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ hy',
        InjectivePlacement.replace_head_other _ _ _ _ _ _ hy']
      show readAt blank (S₀.L y) (S₀.R y) z = readAt blank (S₀.L y) (S₀.R y) (z - 0)
      rw [sub_zero]
  have hpre := Placement.hoare_at hM pe W (Placement.active_replace pe w₀ _)
  -- step 2: run the placed program
  obtain ⟨v₂, S₂, W', ⟨w', hw', hW'⟩, hrep', hu₂, hinp₂, hout₂, hlen₂, hfr₂, m₂, hm₂, he₂⟩ :=
    foreign_exec_frame body _ (placed_idle_injective M ι hι _) hpre v S₀ W rfl hrep
  subst hw'
  have hsweep : ∀ j, sweep (S₂.L (ι j)) (S₂.R (ι j)) = cells (σ₁ j).words := by
    intro j
    refine filter_window (S₂.L (ι j)) (S₂.R (ι j)) (W'.head (ι j)) _ (SS.blank_not_mem_cells _)
      (fun z => ?_)
    have := hrep' (ι j) z
    rw [hW', InjectivePlacement.replace_tape_slot] at this
    rw [hW', ← this]
    rfl
  have hS₂un : ∀ y, (∀ j, ι j ≠ y) → S₂.L y = S.L y ∧ S₂.R y = blank :: S.R y := by
    intro y hy
    have hu : y ∈ unplaced ι := (mem_unplaced ι y).2 hy
    have h₂ := idle_stacks_eq (hfr₂ y hy) (by simp [S₀, hu])
    exact ⟨h₂.1, h₂.2.trans (by simp [S₀, hu])⟩
  -- step 3: normalize the placed registers
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ :=
    normList_exec body (List.ofFn ι) (List.nodup_ofFn.2 hι) v₂ S₂
  -- step 4: unmark the unplaced registers
  have he₄ := dropList_exec body (unplaced ι) (unplaced_nodup ι) v₃ { S₂ with
    L := fun i => if i ∈ List.ofFn ι then [] else S₂.L i
    R := fun i => if i ∈ List.ofFn ι then sweep (S₂.L i) (S₂.R i) else S₂.R i }
  refine ⟨v₃, ((unplaced ι).length + 1) + (m₂ + (n₃ + ((unplaced ι).length + 1))),
    fun y => if y ∈ unplaced ι then
      (if y ∈ List.ofFn ι then sweep (S₂.L y) (S₂.R y) else S₂.R y).tail
      else if y ∈ List.ofFn ι then sweep (S₂.L y) (S₂.R y) else S₂.R y,
    hu₃.trans hu₂, ?_, fun j => ?_, fun y hy => ?_,
    Exec.cast (Exec.seq he₀ (Exec.seq he₂ (Exec.seq he₃ he₄))) rfl ?_⟩
  · rw [List.map_ofFn, List.sum_ofFn] at hn₃
    have hsum : ∑ j, ((fun i => 6 * ((S₂.L i).length + (S₂.R i).length) + 6) ∘ ι) j ≤
        ∑ j, (6 * (S.R (ι j)).length + (12 * k + 6)) := by
      apply Finset.sum_le_sum
      intro j _
      have h1 := hlen₂ (ι j)
      have h2 : S₀.L (ι j) = [] := hL j
      rw [h2, hS₀ι] at h1
      simp only [Function.comp_apply, List.length_nil] at h1 ⊢
      omega
    have hR : ∑ j : Fin s, (6 * (S.R (ι j)).length + (12 * k + 6)) =
        6 * ∑ j, (S.R (ι j)).length + s * (12 * k + 6) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    have key : k * (T + 5) + s * (12 * k + 6) = (T + 12 * s + 5) * k + 6 * s := by ring
    have hu := unplaced_length_le ι
    omega
  · have hm : ι j ∈ List.ofFn ι := List.mem_ofFn.2 ⟨j, rfl⟩
    simp only [hun j, hm, ite_true, ite_false]
    exact hsweep j
  · have hm : y ∉ List.ofFn ι := fun hm => by
      obtain ⟨j, hj⟩ := List.mem_ofFn.1 hm
      exact hy j hj
    have hu : y ∈ unplaced ι := (mem_unplaced ι y).2 hy
    simp only [hu, hm, ite_true, ite_false, (hS₂un y hy).2, List.tail_cons]
  · congr 1
    refine Stacks.ext hinp₂ hout₂ ?_ rfl
    funext y
    by_cases hy : y ∈ List.ofFn ι
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
      simp only [hy, ite_true, hL j]
    · have hy' : ∀ j, ι j ≠ y := fun j hj => hy (List.mem_ofFn.2 ⟨j, hj⟩)
      simp only [hy, ite_false, (hS₂un y hy').1]

end PlacedRun

/-! ### The multiplier over the host alphabet -/

namespace SS

open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule

/-- The binary alphabet `Fin 4` inside the host alphabet `Fin (A + 4)`; every symbol keeps its
code. -/
def code (A : ℕ) : Alphabet.Encoding 0 A where
  encode x := ⟨x.val, by have := x.isLt; omega⟩
  decode y := if h : y.val < 4 then ⟨y.val, by omega⟩ else blank
  decode_encode x := by
    have : x.val < 4 := x.isLt
    simp [this]

/-- Word symbols keep their codes. -/
lemma code_sym (A : ℕ) (o : Option Bool) : (code A).encode (sym o) = sym o := by
  cases o with
  | none => rfl
  | some b => cases b <;> rfl

/-- Encoding commutes with reading a word tape. -/
lemma code_wordTape (A : ℕ) (l : List (Fin (0 + 4))) (z : ℤ) :
    (code A).encode (wordTape l z) = wordTape (l.map (code A).encode) z := by
  unfold wordTape
  split_ifs
  · rw [List.getElem?_map]
    cases l[z.toNat]? <;> rfl
  · rfl

/-- Encoding word cells gives the host word cells. -/
lemma code_cells (A : ℕ) (ws : List (List Bool)) :
    (cells (a := 0) ws).map (code A).encode = cells (a := A) ws := by
  simp only [cells, List.map_map]
  congr 1
  funext o
  exact code_sym A o

/-- Encoding a word-tape bank over `Fin 4` into the host alphabet. -/
lemma mapTapes_enc {t : ℕ} (A : ℕ) (σ : Fin t → WTape) :
    Alphabet.mapTapes (code A) (enc (a := 0) σ) = enc (a := A) σ := by
  refine Placement.Tapes.ext' (fun x => rfl) (fun x => ?_)
  funext z
  show (code A).encode (wordTape (cells (σ x).words) z) = wordTape (cells (σ x).words) z
  rw [code_wordTape, code_cells]

/-- The state count of the compiled cleaned multiplier. -/
abbrev states : ℕ := (compile (a := 0) (by decide) ssClean).1

/-- The cleaned multiplier over the host alphabet with its states embedded in `Fin Q`. -/
def machine (A : ℕ) {Q : ℕ} (hQ : states ≤ Q) : Program 64 Q A :=
  liftQ (Alphabet.program (code A) cleanProgram) hQ

/-- `clean_hoare` over the host alphabet with embedded states. -/
theorem machine_hoare (A : ℕ) {Q : ℕ} (hQ : states ≤ Q) {m a b : ℕ} (hm : 1 ≤ m)
    (ha : a < 2 ^ m) (hb : b < 2 ^ m) :
    HoareTime (machine A hQ) (· = enc (startBank (topN m) a b))
      (· = enc (doneBank (topN m) (a * b))) (cleanBound m) := by
  refine HoareTime.liftQ hQ ((Alphabet.map_hoare (code A) (clean_hoare hm ha hb)).consequence
    (fun w hw => ⟨_, rfl, by rw [hw, mapTapes_enc]⟩) (fun w ⟨o, ho, hw⟩ => ?_) le_rfl)
  rw [hw, ho, mapTapes_enc]

end SS

/-! ### Laying out the input and reading out the product -/

namespace SS

section Pad

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- Push the symbol `x` onto register `i`. -/
def pushSym (i : Fin T) (x : Fin (A + 4)) : Act T Q A U := .push (.rt i) (fun _ => x) .done

/-- Running `pushSym`. -/
lemma pushSym_run (i : Fin T) (x : Fin (A + 4)) (v : HS T Q A U) (S : Stacks T A) :
    (pushSym i x).run (mk v S) = mk v { S with R := Function.update S.R i (x :: S.R i) } := by
  simp [pushSym, Action.run, update_rt]

/-- One step of the padding loop: pop the counter `c` onto `c'`; pop the source `s` onto `s'`
when it is nonempty; push the popped source symbol, or `d` when `s` was empty, onto `u`. -/
def padStep (c c' s s' u : Fin T) (d : Fin (A + 4)) : Act T Q A U :=
  .pop (.rt c) (fun v o => { v with sym := o })
    (.push (.rt c') (fun v => v.sym.getD blank)
      (.pop (.rt s) (fun v o => { v with sym := o })
        (.branch (fun v => v.sym.isSome)
          (.push (.rt s') (fun v => v.sym.getD blank)
            (.push (.rt u) (fun v => v.sym.getD d) (peekR c)))
          (.push (.rt u) (fun v => v.sym.getD d) (peekR c)))))

/-- Five pairwise distinct registers. -/
structure Dist5 (c c' s s' u : Fin T) : Prop where
  h1 : c ≠ c'
  h2 : c ≠ s
  h3 : c ≠ s'
  h4 : c ≠ u
  h5 : c' ≠ s
  h6 : c' ≠ s'
  h7 : c' ≠ u
  h8 : s ≠ s'
  h9 : s ≠ u
  h10 : s' ≠ u

/-- The registers after the padding loop has consumed the counter `cs` and the source `ss`. -/
def padRes (R : Fin T → List (Fin (A + 4))) (c c' s s' u : Fin T) (d : Fin (A + 4))
    (cs ss : List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) := fun k =>
  if k = c then [] else if k = c' then cs.reverse ++ R c' else if k = s then []
  else if k = s' then ss.reverse ++ R s'
  else if k = u then (ss ++ List.replicate (cs.length - ss.length) d).reverse ++ R u else R k

/-- One padding step with a nonempty source. -/
lemma padStep_run_some {c c' s s' u : Fin T} (h : Dist5 c c' s s' u) (d : Fin (A + 4))
    (v : HS T Q A U) (S : Stacks T A) {x y : Fin (A + 4)} {cs ys : List (Fin (A + 4))}
    (hc : S.R c = x :: cs) (hs : S.R s = y :: ys) :
    (padStep c c' s s' u d).run (mk v S) =
      mk { v with sym := some y, flag := cs.head?.isSome } { S with
        R := Function.update (Function.update (Function.update (Function.update
          (Function.update S.R c cs) c' (x :: S.R c')) s ys) s' (y :: S.R s')) u
          (y :: S.R u) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp [padStep, peekR, Action.run, hc, hs, update_rt, Function.update_of_ne, h1, h2, h3, h4, 
    h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm,
    h9.symm, h10.symm]

/-- One padding step with an empty source. -/
lemma padStep_run_none {c c' s s' u : Fin T} (h : Dist5 c c' s s' u) (d : Fin (A + 4))
    (v : HS T Q A U) (S : Stacks T A) {x : Fin (A + 4)} {cs : List (Fin (A + 4))}
    (hc : S.R c = x :: cs) (hs : S.R s = []) :
    (padStep c c' s s' u d).run (mk v S) =
      mk { v with sym := none, flag := cs.head?.isSome } { S with
        R := Function.update (Function.update (Function.update
          (Function.update S.R c cs) c' (x :: S.R c')) s []) u (d :: S.R u) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp [padStep, peekR, Action.run, hc, hs, update_rt, Function.update_of_ne, h1, h2, h4, 
    h1.symm, h2.symm, h4.symm, h5.symm, h7.symm, 
    h9.symm]

/-- Moving one copy of `d` across `List.replicate n d`. -/
lemma replicate_append_cons {α : Type} (n : ℕ) (d : α) (l : List α) :
    List.replicate n d ++ d :: l = d :: (List.replicate n d ++ l) := by
  rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ', List.replicate_succ,
    List.cons_append]

/-- The padding loop consumes the counter `cs` on `c` and the source `ss` on `s`, in exactly
`2 * cs.length + 1` steps. -/
theorem padLoop {c c' s s' u : Fin T} (h : Dist5 c c' s s' u) (d : Fin (A + 4)) :
    ∀ (cs ss : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R c = cs → S.R s = ss → ss.length ≤ cs.length → v.flag = cs.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (padStep c c' s s' u d))) (mk v S) (2 * cs.length + 1)
          (mk v' { S with R := padRes S.R c c' s s' u d cs ss }) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have g1 := h1.symm; have g2 := h2.symm; have g3 := h3.symm; have g4 := h4.symm
  have g5 := h5.symm; have g6 := h6.symm; have g7 := h7.symm; have g8 := h8.symm
  have g9 := h9.symm; have g10 := h10.symm
  intro cs
  induction cs with
  | nil =>
      intro ss v S hc hs hl hf
      have hss : ss = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      subst hss
      refine ⟨v, rfl, ?_⟩
      have : ({ S with R := padRes S.R c c' s s' u d [] [] } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hc hs
          congr 1
          funext k
          simp only [padRes]
          split_ifs with k1 k2 k3 <;> simp_all
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons x cs ih =>
      intro ss v S hc hs hl hf
      rcases ss with _ | ⟨y, ys⟩
      · have hrun := padStep_run_none (U := U) ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ d
          v S hc hs
        obtain ⟨v', hu, he⟩ := ih [] { v with sym := none, flag := cs.head?.isSome } { S with
            R := Function.update (Function.update (Function.update
              (Function.update S.R c cs) c' (x :: S.R c')) s []) u (d :: S.R u) }
          (by simp [Function.update_of_ne, h2, h4, h1])
          (by simp [Function.update_of_ne, h9]) (by simp) rfl
        refine ⟨v', hu, ?_⟩
        refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) (padStep c c' s s' u d) (mk v S)) he)
          (by simp; ring) ?_
        congr 2
        funext k
        simp only [padRes]
        by_cases k1 : k = c
        · rw [k1]; simp
        by_cases k2 : k = c'
        · rw [k2]; simp [h5, h7, g1, 
            Function.update_of_ne, 
            ]
        by_cases k3 : k = s
        · rw [k3]; simp [g2, g5,
            
            ]
        by_cases k4 : k = s'
        · rw [k4]; simp [h10, g3, 
            g6, g8, Function.update_of_ne, 
            ]
        by_cases k5 : k = u
        · rw [k5]; simp [g4, 
            g7, g9, g10, replicate_append_cons,
            List.replicate_succ]
        · simp [k1, k2, k3, k4, k5, Function.update_of_ne]
      · have hrun := padStep_run_some (U := U) ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ d
          v S hc hs
        obtain ⟨v', hu, he⟩ := ih ys { v with sym := some y, flag := cs.head?.isSome } { S with
            R := Function.update (Function.update (Function.update (Function.update
              (Function.update S.R c cs) c' (x :: S.R c')) s ys) s' (y :: S.R s')) u (y :: S.R u) }
          (by simp [Function.update_of_ne, h2, h4, h1, h3])
          (by simp [Function.update_of_ne, h9, h8])
          (by simpa using hl) rfl
        refine ⟨v', hu, ?_⟩
        refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) (padStep c c' s s' u d) (mk v S)) he)
          (by simp; ring) ?_
        congr 2
        funext k
        simp only [padRes]
        by_cases k1 : k = c
        · rw [k1]; simp
        by_cases k2 : k = c'
        · rw [k2]; simp [h5, h6, h7, g1, 
            Function.update_of_ne, 
            ]
        by_cases k3 : k = s
        · rw [k3]; simp [g2, g5,
            
            ]
        by_cases k4 : k = s'
        · rw [k4]; simp [h10, g3, 
            g6, g8, Function.update_of_ne, 
            ]
        by_cases k5 : k = u
        · rw [k5]; simp [g4, 
            g7, g9, g10, 
            ]
        · simp [k1, k2, k3, k4, k5, Function.update_of_ne]

/-- Push onto register `t` a copy of register `s` padded with `d` to the length of register `c`,
through the empty registers `c'`, `s'`, `u`; `c` and `s` are restored. -/
def padCopy (c s t c' s' u : Fin T) (d : Fin (A + 4)) : Pr P T Q A U :=
  .seq (.act (peekR c)) (.seq (.loop (·.flag) (.act (padStep c c' s s' u d)))
    (.seq (moveR c' c id) (.seq (moveR s' s id) (moveR u t id))))

/-- A padded copy: register `t` receives `S.R s` padded with `d` to the length of `S.R c`, every
other register is unchanged. -/
theorem padCopy_exec {c s t c' s' u : Fin T} (h : Dist5 c c' s s' u) (htc : t ≠ c) (hts : t ≠ s)
    (htc' : t ≠ c') (hts' : t ≠ s') (htu : t ≠ u) (d : Fin (A + 4)) (v : HS T Q A U)
    (S : Stacks T A) (hc' : S.R c' = []) (hs' : S.R s' = []) (hu : S.R u = [])
    (hl : (S.R s).length ≤ (S.R c).length) :
    ∃ v', v'.user = v.user ∧
      Exec body (padCopy c s t c' s' u d) (mk v S) (6 * (S.R c).length + 2 * (S.R s).length + 8)
        (mk v' { S with
          R := Function.update S.R t
            ((S.R s ++ List.replicate ((S.R c).length - (S.R s).length) d) ++ S.R t) }) := by
  have hd := h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have g1 := h1.symm; have g2 := h2.symm; have g3 := h3.symm; have g4 := h4.symm
  have g5 := h5.symm; have g6 := h6.symm; have g7 := h7.symm; have g8 := h8.symm
  have g9 := h9.symm; have g10 := h10.symm
  have f1 := htc.symm; have f2 := hts.symm; have f3 := htc'.symm; have f4 := hts'.symm
  have f5 := htu.symm
  set L := (S.R c).length
  set ls := (S.R s).length
  obtain ⟨v₁, hu₁, he₁⟩ := padLoop body hd d (S.R c) (S.R s) { v with flag := (S.R c).head?.isSome }
    S rfl rfl hl rfl
  set S₁ : Stacks T A := { S with R := padRes S.R c c' s s' u d (S.R c) (S.R s) } with hS₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body c' c h1.symm id v₁ S₁
  set S₂ : Stacks T A := { S₁ with R := movedR S₁.R c' c id (S₁.R c') } with hS₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body s' s h8.symm id v₂ S₂
  set S₃ : Stacks T A := { S₂ with R := movedR S₂.R s' s id (S₂.R s') } with hS₃
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body u t htu.symm id v₃ S₃
  have l₁ : (S₁.R c').length = L := by simp [S₁, padRes, g1, hc', L]
  have l₂ : (S₂.R s').length = ls := by
    simp [S₂, S₁, movedR, padRes, Function.update_of_ne, g3, g6, g8, hs', ls]
  have l₃ : (S₃.R u).length = L := by
    simp [S₃, S₂, S₁, movedR, padRes, Function.update_of_ne, g4, g7, g9, g10, hu, 
      L]
    omega
  refine ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)), Exec.cast
    (Exec.seq (peekR_run c v S ▸ Exec.act (body := body) (peekR c) (mk v S))
      (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)))) ?_ ?_⟩
  · rw [l₁, l₂, l₃]; ring
  · congr 2
    funext k
    simp only [S₃, S₂, S₁, movedR]
    by_cases k1 : k = c
    · rw [k1]; simp [padRes, Function.update_of_ne, h2, h3, h4, g1,
        g2, g3, g4, g5, g6, g7, g8, g9, g10, f1, hc']
    by_cases k2 : k = c'
    · rw [k2]; simp [padRes, Function.update_of_ne, h5, h6, h7, g1,
        g2, g3, g4, g5, g6, g7, g8, g9, g10, f3, hc']
    by_cases k3 : k = s
    · rw [k3]; simp [padRes, Function.update_of_ne, h9, g1,
        g2, g3, g4, g5, g6, g7, g8, g9, g10, f2, hs']
    by_cases k4 : k = s'
    · rw [k4]; simp [padRes, Function.update_of_ne, h10, g1,
        g2, g3, g4, g5, g6, g7, g8, g9, g10, f4, hs']
    by_cases k5 : k = u
    · rw [k5]; simp [padRes, Function.update_of_ne, g1,
        g2, g3, g4, g5, g6, g7, g8, g9, g10, f5, hu]
    by_cases k6 : k = t
    · rw [k6]
      have e1 : padRes S.R c c' s s' u d (S.R c) (S.R s) t = S.R t := by
        simp [padRes, htc, hts, htc', hts', htu]
      rw [Function.update_self, Function.update_self]
      have e2 : S₃.R u = (S.R s ++ List.replicate (L - ls) d).reverse := by
        simp [S₃, S₂, S₁, movedR, padRes, Function.update_of_ne, g4, g7, g9, g10, hu, 
          L, ls]
      have e3 : S₃.R t = S.R t := by
        simp only [S₃, S₂, S₁, movedR, Function.update_of_ne hts, Function.update_of_ne hts',
          Function.update_of_ne htc, Function.update_of_ne htc', e1]
      simp only [S₃, S₂, S₁, movedR] at e2 e3
      rw [e2, e3, List.map_id, List.reverse_reverse]
    · simp [padRes, Function.update_of_ne, k1, k2, k3, k4, k5, k6]

/-- Lay out the multiplier's input from host registers: onto `rI` the two padded operands from
`xa` and `xb`, each followed by `bitSymbol false` and `separator`; onto `rN` a unary copy of `xn`
in `bitSymbol true`, followed by `separator`. `rE` is an empty register; `s₁`, `s₂`, `s₃` are
empty scratch registers. -/
def layout (rI rN rE s₁ s₂ s₃ xa xb xn : Fin T) : Pr P T Q A U :=
  .seq (.act (pushSym rI separator)) <| .seq (.act (pushSym rI (bitSymbol false))) <|
  .seq (padCopy xn xb rI s₁ s₂ s₃ (bitSymbol false)) <|
  .seq (.act (pushSym rI separator)) <| .seq (.act (pushSym rI (bitSymbol false))) <|
  .seq (padCopy xn xa rI s₁ s₂ s₃ (bitSymbol false)) <|
  .seq (.act (pushSym rN separator)) (padCopy xn rE rN s₁ s₂ s₃ (bitSymbol true))

/-- The list `x` padded with `d` to length `L`. -/
def padded (x : List (Fin (A + 4))) (L : ℕ) (d : Fin (A + 4)) : List (Fin (A + 4)) :=
  x ++ List.replicate (L - x.length) d

/-- The layout: `rI` receives both padded operands with their trailing `bitSymbol false` and
`separator`, `rN` receives `(S.R xn).length` symbols `bitSymbol true` and `separator`, every
other register is unchanged. -/
theorem layout_exec {rI rN rE s₁ s₂ s₃ xa xb xn : Fin T}
    (hda : Dist5 xn s₁ xa s₂ s₃) (hdb : Dist5 xn s₁ xb s₂ s₃) (hde : Dist5 xn s₁ rE s₂ s₃)
    (hI : ∀ y ∈ [xn, xa, xb, s₁, s₂, s₃, rN, rE], rI ≠ y) (hN : ∀ y ∈ [xn, rE, s₁, s₂, s₃], rN ≠ y)
    (v : HS T Q A U) (S : Stacks T A) (h₁ : S.R s₁ = []) (h₂ : S.R s₂ = []) (h₃ : S.R s₃ = [])
    (hE : S.R rE = []) (ha : (S.R xa).length ≤ (S.R xn).length)
    (hb : (S.R xb).length ≤ (S.R xn).length) :
    ∃ v', v'.user = v.user ∧
      Exec body (layout rI rN rE s₁ s₂ s₃ xa xb xn) (mk v S)
        (18 * (S.R xn).length + 2 * (S.R xa).length + 2 * (S.R xb).length + 29)
        (mk v' { S with
          R := Function.update (Function.update S.R rI
            (padded (S.R xa) (S.R xn).length (bitSymbol false) ++ bitSymbol false :: separator ::
              (padded (S.R xb) (S.R xn).length (bitSymbol false) ++ bitSymbol false :: separator ::
                S.R rI))) rN
            (List.replicate (S.R xn).length (bitSymbol true) ++ separator :: S.R rN) }) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hI hN
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hI
  obtain ⟨n1, n2, n3, n4, n5⟩ := hN
  set L := (S.R xn).length
  set f : Fin (A + 4) := bitSymbol false
  -- the eight steps
  set S₁ : Stacks T A := { S with R := Function.update S.R rI (separator :: S.R rI) }
  have e₁ := Exec.act (body := body) (pushSym rI separator) (mk v S)
  rw [pushSym_run] at e₁
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R rI (f :: S₁.R rI) }
  have e₂ := Exec.act (body := body) (pushSym rI f) (mk v S₁)
  rw [pushSym_run] at e₂
  obtain ⟨v₃, u₃, e₃⟩ := padCopy_exec body hdb i1 i3 i4 i5 i6 f v S₂
    (by simp [S₂, S₁, Function.update_of_ne i4.symm, h₁])
    (by simp [S₂, S₁, Function.update_of_ne i5.symm, h₂])
    (by simp [S₂, S₁, Function.update_of_ne i6.symm, h₃])
    (by simpa [S₂, S₁, Function.update_of_ne i3.symm, Function.update_of_ne i1.symm] using hb)
  set S₃ : Stacks T A := { S₂ with
    R := Function.update S₂.R rI
      ((S₂.R xb ++ List.replicate ((S₂.R xn).length - (S₂.R xb).length) f) ++ S₂.R rI) }
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R rI (separator :: S₃.R rI) }
  have e₄ := Exec.act (body := body) (pushSym rI separator) (mk v₃ S₃)
  rw [pushSym_run] at e₄
  set S₅ : Stacks T A := { S₄ with R := Function.update S₄.R rI (f :: S₄.R rI) }
  have e₅ := Exec.act (body := body) (pushSym rI f) (mk v₃ S₄)
  rw [pushSym_run] at e₅
  obtain ⟨v₆, u₆, e₆⟩ := padCopy_exec body hda i1 i2 i4 i5 i6 f v₃ S₅
    (by simp [S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i4.symm, h₁])
    (by simp [S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i5.symm, h₂])
    (by simp [S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i6.symm, h₃])
    (by simpa [S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i2.symm, Function.update_of_ne i1.symm]
      using ha)
  set S₆ : Stacks T A := { S₅ with
    R := Function.update S₅.R rI
      ((S₅.R xa ++ List.replicate ((S₅.R xn).length - (S₅.R xa).length) f) ++ S₅.R rI) }
  set S₇ : Stacks T A := { S₆ with R := Function.update S₆.R rN (separator :: S₆.R rN) }
  have e₇ := Exec.act (body := body) (pushSym rN separator) (mk v₆ S₆)
  rw [pushSym_run] at e₇
  obtain ⟨v₈, u₈, e₈⟩ := padCopy_exec body hde n1 n2 n3 n4 n5 (bitSymbol true) v₆ S₇
    (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i4.symm,
      Function.update_of_ne n3.symm, h₁])
    (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i5.symm,
      Function.update_of_ne n4.symm, h₂])
    (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i6.symm,
      Function.update_of_ne n5.symm, h₃])
    (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i8.symm,
      Function.update_of_ne n2.symm, hE])
  refine ⟨v₈, u₈.trans (u₆.trans u₃), Exec.cast
    (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ e₈))))))) ?_ ?_⟩
  · simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i1.symm, Function.update_of_ne i2.symm,
      Function.update_of_ne i3.symm, Function.update_of_ne i8.symm, Function.update_of_ne n1.symm,
      Function.update_of_ne n2.symm, hE, L]
    ring
  · congr 2
    funext k
    by_cases k1 : k = rN
    · rw [k1]
      simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i1.symm,
        Function.update_of_ne i8.symm, Function.update_of_ne n1.symm,
        Function.update_of_ne n2.symm, hE, L, i7.symm]
    by_cases k2 : k = rI
    · rw [k2]
      simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Function.update_of_ne i1.symm,
        Function.update_of_ne i2.symm, Function.update_of_ne i3.symm, i7,
        padded, L, f]
    · simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Function.update_of_ne k1, Function.update_of_ne k2]

/-- Move the content of register `rI` without its last symbol onto register `xc`, through the empty
register `s₁`. -/
def readOut (rI s₁ xc : Fin T) : Pr P T Q A U :=
  .seq (moveR rI s₁ id) (.seq (.act (dropStep s₁)) (moveR s₁ xc id))

/-- Reading out: `xc` receives the content of `rI` without its last symbol, `rI` ends empty,
every other register is unchanged. -/
theorem readOut_exec {rI s₁ xc : Fin T} (h1 : rI ≠ s₁) (h2 : rI ≠ xc) (h3 : s₁ ≠ xc)
    (v : HS T Q A U) (S : Stacks T A) {l : List (Fin (A + 4))} {x : Fin (A + 4)}
    (hI : S.R rI = l ++ [x]) (hs : S.R s₁ = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (readOut rI s₁ xc) (mk v S) (4 * l.length + 7)
        (mk v' { S with R := Function.update (Function.update S.R rI []) xc (l ++ S.R xc) }) := by
  obtain ⟨v₁, u₁, e₁⟩ := moveR_exec body rI s₁ h1 id v S
  set S₁ : Stacks T A := { S with R := movedR S.R rI s₁ id (S.R rI) }
  have e₂ := Exec.act (body := body) (dropStep s₁) (mk v₁ S₁)
  rw [show (dropStep s₁ : Act T Q A U).run (mk v₁ S₁) =
      mk v₁ { S₁ with R := Function.update S₁.R s₁ (S₁.R s₁).tail } by
    simp [dropStep, Action.run, update_rt]] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R s₁ (S₁.R s₁).tail }
  obtain ⟨v₃, u₃, e₃⟩ := moveR_exec body s₁ xc h3 id v₁ S₂
  have hs₂ : S₂.R s₁ = l.reverse := by simp [S₂, S₁, movedR, hI, hs]
  refine ⟨v₃, u₃.trans u₁, Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃)) ?_ ?_⟩
  · rw [hs₂, hI]; simp; ring
  · congr 2
    rw [hs₂]
    funext k
    by_cases k1 : k = xc
    · rw [k1]; simp [S₂, S₁, movedR, h2.symm, h3.symm, Function.update_of_ne]
    by_cases k2 : k = s₁
    · rw [k2]; simp [S₂, S₁, movedR, h1.symm, h3, hs, Function.update_of_ne]
    · simp [S₂, S₁, movedR, k1, k2, Function.update_of_ne]

end Pad

end SS

/-! ### Bit formats -/

namespace SS

section Formats

open IntegerMultBounds.Schoenhage

variable {A : ℕ}

/-- The host numeral bits are the vendored words' bits. -/
lemma binBits_eq_bits (n v : ℕ) : binBits n v = bits n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [binBits_succ, ih, Nat.testBit_zero]; rfl

/-- Padding a binary numeral with zero bits lengthens it. -/
lemma binBits_append_replicate {m L a : ℕ} (ha : a < 2 ^ m) (hmL : m ≤ L) :
    binBits m a ++ List.replicate (L - m) false = binBits L a := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  by_cases hi : i < m
  · rw [List.getElem_append_left (by simpa using hi)]
    simp [binBits]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_replicate, binBits, List.getElem_ofFn]
    exact (Nat.testBit_eq_false_of_lt (ha.trans_le (Nat.pow_le_pow_right (by norm_num)
      (by omega)))).symm

/-- `binBits_append_replicate` on register symbols. -/
lemma binSyms_append_replicate {m L a : ℕ} (ha : a < 2 ^ m) (hmL : m ≤ L) :
    (binSyms m a : List (Fin (A + 4))) ++ List.replicate (L - m) (bitSymbol false) =
      binSyms L a := by
  rw [binSyms_eq, binSyms_eq, ← binBits_append_replicate ha hmL, List.map_append,
    List.map_replicate]

/-- The cells of no word. -/
lemma cells_nil' : cells (a := A) [] = [] := rfl

/-- The cells of a word list: the first word's bits, a separator, the rest. -/
lemma cells_cons' (w : List Bool) (ws : List (List Bool)) :
    cells (a := A) (w :: ws) = w.map bitSymbol ++ separator :: cells ws := by
  simp [cells, syms_cons, sym, Function.comp_def]

/-- The cells of a residue word. -/
lemma cells_rwd (N v : ℕ) (ws : List (List Bool)) :
    cells (a := A) (rwd N v :: ws) = binSyms (N + 1) v ++ separator :: cells ws := by
  rw [cells_cons', binSyms_eq, binBits_eq_bits]; rfl

/-- The cells of a unary word. -/
lemma cells_ones (N : ℕ) :
    cells (a := A) [ones N] = List.replicate N (bitSymbol true) ++ [separator] := by
  rw [cells_cons', ones, List.map_replicate]; rfl

/-- The operand padded by `layout`, with its trailing zero bit. -/
lemma padded_binSyms {m N a : ℕ} (ha : a < 2 ^ m) (hmN : m ≤ N) (l : List (Fin (A + 4))) :
    padded (binSyms m a) N (bitSymbol false) ++ bitSymbol false :: l = binSyms (N + 1) a ++ l := by
  rw [padded, length_binSyms, ← binSyms_append_replicate ha (by omega : m ≤ N + 1),
    show N + 1 - m = (N - m) + 1 by omega, List.replicate_succ']
  simp

/-- The product word read back, in terms of its low `2 * m` bits. -/
lemma binSyms_product {m N p : ℕ} (hp : p < 2 ^ (2 * m)) (hmN : 2 * m ≤ N + 1) :
    (binSyms (N + 1) p : List (Fin (A + 4))) =
      binSyms (2 * m) p ++ List.replicate (N + 1 - 2 * m) (bitSymbol false) :=
  (binSyms_append_replicate hp hmN).symm

end Formats

end SS

/-! ### The host multiplier -/

section Main

open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule
  IntegerMultBounds.Schoenhage.Tp SS

variable {T Q A : ℕ} {U F : Type}

/-- The step bound of one call of `ssMul` per unit of `T + 773`: the cleaned multiplier's
bound `SS.cleanBound m` plus two. -/
def ssCostBound (m : ℕ) : ℕ := SS.cleanBound m + 2

/-- Multiply the operands in registers `xa`, `xb` by the cleaned Schönhage–Strassen multiplier
placed on the registers `ι`; register `xn` holds the multiplier size `topN m` in unary, and the
product goes onto register `xc`. -/
def ssMul (ι : Fin 64 → Fin T) (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (xa xb xn xc : Fin T) : Pr F T Q A U :=
  .seq (layout (ι tIn) (ι pN) (ι 3) (ι 0) (ι 1) (ι 2) xa xb xn)
    (.seq (placedRun (SS.machine A hQ) ι hι hT) (readOut (ι tIn) (ι 0) xc))

/-- Running `ssMul`. The registers `ι j` are empty (both stacks); `xa`, `xb`, `xn`, `xc` lie
outside the range of `ι`, and `xn` differs from `xa` and `xb`; `xa`, `xb` hold `binSyms m a`,
`binSyms m b` with `a, b < 2 ^ m` and `1 ≤ m`; `xn` holds `topN m` symbols. Afterwards
`binSyms (topN m + 1) (a * b)` sits on top of `xc`, every other stack and the `user` component
are unchanged, and at most `(T + 773) * ssCostBound m + 164 * m + 463` host steps were taken. The
factor `T` comes from `foreign`, which scans every host tape once per simulated transition, and
from the two passes over the unplaced registers. -/
theorem ssMul_exec (body : F → Pr F T Q A U) (ι : Fin 64 → Fin T) (hι : Function.Injective ι)
    (hT : 64 ≤ T) (hQ : SS.states ≤ Q) {xa xb xn xc : Fin T}
    (hxa : ∀ j, ι j ≠ xa) (hxb : ∀ j, ι j ≠ xb) (hxn : ∀ j, ι j ≠ xn) (hxc : ∀ j, ι j ≠ xc)
    (hna : xn ≠ xa) (hnb : xn ≠ xb) {m a b : ℕ} (hm : 1 ≤ m) (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (v : HS T Q A U) (S : Stacks T A) (hL : ∀ j, S.L (ι j) = []) (hR : ∀ j, S.R (ι j) = [])
    (hSa : S.R xa = binSyms m a) (hSb : S.R xb = binSyms m b) (hSn : (S.R xn).length = topN m) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (T + 773) * ssCostBound m + 164 * m + 463 ∧
      Exec body (ssMul ι hι hT hQ xa xb xn xc) (mk v S) n
        (mk v' { S with
          R := Function.update S.R xc (binSyms (topN m + 1) (a * b) ++ S.R xc) }) := by
  obtain ⟨hlt, hle, -⟩ := topN_facts hm
  set N := topN m with hN
  have hmN : m ≤ N := by omega
  have i0 : ∀ {j k : Fin 64}, j ≠ k → ι j ≠ ι k := fun h => hι.ne h
  -- step 1: lay out the start bank
  obtain ⟨v₁, u₁, e₁⟩ := layout_exec body (rI := ι tIn) (rN := ι pN) (rE := ι 3) (s₁ := ι 0)
    (s₂ := ι 1) (s₃ := ι 2) (xa := xa) (xb := xb) (xn := xn)
    ⟨(hxn 0).symm, hna, (hxn 1).symm, (hxn 2).symm, hxa 0, i0 (by decide), i0 (by decide),
      (hxa 1).symm, (hxa 2).symm, i0 (by decide)⟩
    ⟨(hxn 0).symm, hnb, (hxn 1).symm, (hxn 2).symm, hxb 0, i0 (by decide), i0 (by decide),
      (hxb 1).symm, (hxb 2).symm, i0 (by decide)⟩
    ⟨(hxn 0).symm, (hxn 3).symm, (hxn 1).symm, (hxn 2).symm, i0 (by decide), i0 (by decide),
      i0 (by decide), i0 (by decide), i0 (by decide), i0 (by decide)⟩
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hxn _, hxa _, hxb _, i0 (by decide), i0 (by decide), i0 (by decide), i0 (by decide),
        i0 (by decide)⟩)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hxn _, i0 (by decide), i0 (by decide), i0 (by decide), i0 (by decide)⟩)
    v S (hR 0) (hR 1) (hR 2) (hR 3) (by rw [hSa, hSn]; simpa using hmN)
    (by rw [hSb, hSn]; simpa using hmN)
  rw [hSa, hSb, hSn, length_binSyms, length_binSyms, padded_binSyms ha hmN,
    padded_binSyms hb hmN, hR, hR] at e₁
  set S₁ : Stacks T A := { S with
    R := Function.update (Function.update S.R (ι tIn)
      (binSyms (N + 1) a ++ separator :: (binSyms (N + 1) b ++ [separator]))) (ι pN)
      (List.replicate N (bitSymbol true) ++ [separator]) } with hS₁
  have hIN : ι tIn ≠ ι pN := i0 (by decide)
  have hTP : (tIn : Fin 64) ≠ pN := by decide
  have hstart : ∀ j, S₁.R (ι j) = cells (SS.startBank N a b j).right := by
    intro j
    by_cases j1 : j = tIn
    · rw [j1]
      simp [S₁, SS.startBank, Function.update_of_ne hIN, Function.update_of_ne hTP, cells_rwd,
        cells_nil']
    by_cases j2 : j = pN
    · rw [j2]
      simp [S₁, SS.startBank, cells_ones]
    · simp [S₁, SS.startBank, Function.update_of_ne j1, Function.update_of_ne j2,
        Function.update_of_ne (i0 j1), Function.update_of_ne (i0 j2), hR, cells_nil', emp]
  -- step 2: run the placed multiplier
  obtain ⟨v₂, n₂, R', u₂, hn₂, hR'ι, hR'o, e₂⟩ := placedRun_exec body (SS.machine A hQ) ι hι hT
    (SS.machine_hoare A hQ hm ha hb) (fun j => by
      simp only [SS.startBank, Function.update_apply]
      split_ifs <;> rfl) v₁ S₁ hL hstart
  -- step 3: read the product back
  have hout : R' (ι tIn) = binSyms (N + 1) (a * b) ++ [separator] := by
    rw [hR'ι]
    simp [SS.doneBank, WTape.words, cells_rwd, cells_nil']
    rfl
  have h0 : R' (ι 0) = [] := by
    rw [hR'ι]
    simp [SS.doneBank, WTape.words, Function.update_of_ne (show (0 : Fin 64) ≠ tIn by decide),
      emp, cells_nil']
  obtain ⟨v₃, u₃, e₃⟩ := readOut_exec body (rI := ι tIn) (s₁ := ι 0) (xc := xc) (i0 (by decide))
    (hxc _) (hxc _) v₂ { S₁ with R := R' } hout h0
  refine ⟨v₃, _, u₃.trans (u₂.trans u₁), ?_, Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃)) rfl ?_⟩
  · have hsum : ∑ j, (S₁.R (ι j)).length = 3 * N + 5 := by
      rw [Finset.sum_eq_add tIn pN hTP (fun c _ hc => ?_) (by simp) (by simp)]
      · simp [S₁, Function.update_of_ne hIN]
        ring
      · simp [S₁, Function.update_of_ne (i0 hc.1), Function.update_of_ne (i0 hc.2), hR]
    rw [hsum, show T + 12 * 64 + 5 = T + 773 by norm_num] at hn₂
    simp only [length_binSyms]
    rw [ssCostBound, Nat.mul_add (T + 773)]
    generalize (T + 773) * SS.cleanBound m = X at *
    omega
  · congr 1
    refine Stacks.ext rfl rfl rfl ?_
    have hS₁o : ∀ y, y ≠ ι tIn → y ≠ ι pN → S₁.R y = S.R y := fun y h1 h2 => by
      simp [S₁, Function.update_of_ne h1, Function.update_of_ne h2]
    have hxcR : R' xc = S.R xc := (hR'o xc (hxc)).trans (hS₁o xc (hxc _).symm (hxc _).symm)
    funext y
    dsimp only
    by_cases y1 : y = xc
    · rw [y1, Function.update_self, Function.update_self, hxcR]
    by_cases y2 : ∃ j, ι j = y
    · obtain ⟨j, rfl⟩ := y2
      rw [Function.update_of_ne y1, Function.update_of_ne y1, hR j]
      by_cases j1 : j = tIn
      · rw [j1, Function.update_self]
      · rw [Function.update_of_ne (i0 j1), hR'ι]
        simp [SS.doneBank, WTape.words, Function.update_of_ne j1, emp, cells_nil']
    · have y2' : ∀ j, ι j ≠ y := fun j hj => y2 ⟨j, hj⟩
      rw [Function.update_of_ne y1, Function.update_of_ne y1, Function.update_of_ne (y2' _).symm,
        hR'o y y2', hS₁o y (y2' _).symm (y2' _).symm]

end Main

/-! ### The bound in logarithms -/

namespace SS

open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule

/-- `bitlen (4 m) ≤ log m + 3`. -/
theorem bitlen_four_le (m : ℕ) : bitlen (4 * m) ≤ Nat.log 2 m + 3 := by
  unfold bitlen
  rw [Nat.size_le]
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
  rw [pow_succ] at h
  have : 2 ^ (Nat.log 2 m + 3) = 2 ^ Nat.log 2 m * 8 := by rw [pow_add]; norm_num
  omega

/-- `bitlen (bitlen (4 m)) ≤ log log m + 3`. -/
theorem bitlen_bitlen_four_le (m : ℕ) :
    bitlen (bitlen (4 * m)) ≤ Nat.log 2 (Nat.log 2 m) + 3 := by
  refine (Nat.size_le_size (bitlen_four_le m)).trans ?_
  rw [Nat.size_le]
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Nat.log 2 m)
  rw [pow_succ] at h
  have h1 : 1 ≤ 2 ^ Nat.log 2 (Nat.log 2 m) := Nat.one_le_two_pow
  have : 2 ^ (Nat.log 2 (Nat.log 2 m) + 3) = 2 ^ Nat.log 2 (Nat.log 2 m) * 8 := by
    rw [pow_add]; norm_num
  omega

end SS

section Logs

open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule

/-- `m (log m + 1) (log log m + 1)`, with binary logarithms rounded down. -/
def mLogLog (m : ℕ) : ℕ := m * (Nat.log 2 m + 1) * (Nat.log 2 (Nat.log 2 m) + 1)

/-- `m ≤ m (log m + 1) (log log m + 1)`. -/
lemma le_mLogLog (m : ℕ) : m ≤ mLogLog m := by
  unfold mLogLog
  calc m = m * 1 * 1 := by ring
    _ ≤ m * (Nat.log 2 m + 1) * (Nat.log 2 (Nat.log 2 m) + 1) := by gcongr <;> omega

/-- The multiplier's bound is `O(m log m log log m)`. -/
theorem ssCostBound_le {m : ℕ} (hm : 1 ≤ m) :
    ssCostBound m ≤ (200 * costC cA cB cC0 + 57483) * mLogLog m := by
  have h1 : bitlen (4 * m) + 1 ≤ 4 * (Nat.log 2 m + 1) := by
    have := SS.bitlen_four_le m; omega
  have h2 : 3 * bitlen (bitlen (4 * m)) + 1 ≤ 10 * (Nat.log 2 (Nat.log 2 m) + 1) := by
    have := SS.bitlen_bitlen_four_le m; omega
  have h3 : 4 * m + 1 ≤ 5 * m := by omega
  have hP := le_mLogLog m
  have key : costC cA cB cC0 * (4 * m + 1) * (bitlen (4 * m) + 1) *
      (3 * bitlen (bitlen (4 * m)) + 1) ≤ 200 * costC cA cB cC0 * mLogLog m := by
    calc costC cA cB cC0 * (4 * m + 1) * (bitlen (4 * m) + 1) * (3 * bitlen (bitlen (4 * m)) + 1)
        ≤ costC cA cB cC0 * (5 * m) * (4 * (Nat.log 2 m + 1)) *
            (10 * (Nat.log 2 (Nat.log 2 m) + 1)) := by gcongr
      _ = 200 * costC cA cB cC0 * mLogLog m := by unfold mLogLog; ring
  unfold ssCostBound SS.cleanBound
  generalize costC cA cB cC0 * (4 * m + 1) * (bitlen (4 * m) + 1) *
      (3 * bitlen (bitlen (4 * m)) + 1) = X at *
  generalize costC cA cB cC0 = C at *
  generalize mLogLog m = P at *
  nlinarith

/-- The constant of the `O((T + 1) m log m log log m)` step bound of `ssMul`. -/
def ssMulConst : ℕ := 773 * (200 * costC cA cB cC0 + 57483) + 627

/-- The arithmetic of `ssMul_cost_le`. -/
lemma cost_arith {T m B K P : ℕ} (hB : B ≤ K * P) (hP : m ≤ P) (hm : 1 ≤ m) :
    (T + 773) * B + 164 * m + 463 ≤ (773 * K + 627) * (T + 1) * P := by
  have h1 : (T + 773) * B ≤ (T + 773) * (K * P) := Nat.mul_le_mul_left _ hB
  have h2 : (T + 773) * (K * P) ≤ 773 * (T + 1) * (K * P) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : 164 * m + 463 ≤ 627 * (T + 1) * P := by nlinarith
  calc (T + 773) * B + 164 * m + 463 ≤ 773 * (T + 1) * (K * P) + 627 * (T + 1) * P := by omega
    _ = (773 * K + 627) * (T + 1) * P := by ring

/-- The step bound of `ssMul_exec` is `O((T + 1) m log m log log m)`. -/
theorem ssMul_cost_le (T : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    (T + 773) * ssCostBound m + 164 * m + 463 ≤ ssMulConst * (T + 1) * mLogLog m :=
  cost_arith (ssCostBound_le hm) (le_mLogLog m) hm

end Logs

section MainLog

open IntegerMultBounds.Schoenhage.Schedule

variable {T Q A : ℕ} {U F : Type}

/-- `ssMul_exec` with the step bound `ssMulConst * (T + 1) * (m (log m + 1) (log log m + 1))`. -/
theorem ssMul_exec_log (body : F → Pr F T Q A U) (ι : Fin 64 → Fin T) (hι : Function.Injective ι)
    (hT : 64 ≤ T) (hQ : SS.states ≤ Q) {xa xb xn xc : Fin T}
    (hxa : ∀ j, ι j ≠ xa) (hxb : ∀ j, ι j ≠ xb) (hxn : ∀ j, ι j ≠ xn) (hxc : ∀ j, ι j ≠ xc)
    (hna : xn ≠ xa) (hnb : xn ≠ xb) {m a b : ℕ} (hm : 1 ≤ m) (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (v : HS T Q A U) (S : Stacks T A) (hL : ∀ j, S.L (ι j) = []) (hR : ∀ j, S.R (ι j) = [])
    (hSa : S.R xa = binSyms m a) (hSb : S.R xb = binSyms m b) (hSn : (S.R xn).length = topN m) :
    ∃ v' n, v'.user = v.user ∧ n ≤ ssMulConst * (T + 1) * mLogLog m ∧
      Exec body (ssMul ι hι hT hQ xa xb xn xc) (mk v S) n
        (mk v' { S with
          R := Function.update S.R xc (binSyms (topN m + 1) (a * b) ++ S.R xc) }) := by
  obtain ⟨v', n, hu, hn, he⟩ := ssMul_exec body ι hι hT hQ hxa hxb hxn hxc hna hnb hm ha hb v S
    hL hR hSa hSb hSn
  exact ⟨v', n, hu, hn.trans (ssMul_cost_le T hm), he⟩

end MainLog

end

end IntegerMultBounds.MathlibTM2.Host
