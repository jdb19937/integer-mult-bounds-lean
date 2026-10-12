module

public import IntegerMultBounds.MathlibTM2.Host.Stream

/-!
# Routing stream blocks by a block counter

`routeBlocks` cuts the stream in register `src` into blocks of `B` symbols and pushes block `n`
onto register `dst (sel (n % W))`. `mergeBlocks` is the inverse direction: for block index
`n = 0, 1, …` it pops one block from `srcs (sel (n % W))` and pushes it onto one register.

Devices shared by both programs:

* The block length `B` is the length of a counter register `ctr`. Transferring each symbol of a
  block also moves one symbol from `ctr` to `tmp`; after the block, `moveR` moves `tmp` back
  onto `ctr`.
* The block index modulo `W` is a symbol in the scratch slot `scan cs`. It starts at `0` and
  advances by `nextC W` after each block, so during block `n` it has value `n % W`
  (`nextC_val`, for `1 ≤ W ≤ A + 4`).
* The destination of a symbol is selected by `selDispatch`, a chain of `Action.branch` over
  `List.finRange nd` testing `sel (scan cs).val`.

`routeBlocks` loops while `src` is nonempty (this needs `1 ≤ B`). `mergeBlocks` counts blocks
with a register `cnt` holding one symbol per block: each block moves one symbol of `cnt` onto
`ctmp`, and a final `moveR` moves `ctmp` back onto `cnt`.

The block lists are `blocksTo` (blocks with index `n < nb` routed to `d`, in increasing order)
and its relative form `blocksAt`. Step counts are exact:

* `routeBlocks_exec`: `4 * (nb * B) + 6 * nb + 2` steps;
* `mergeBlocks_exec`: `4 * (nb * B) + 8 * nb + 4` steps;
* `roundTrip_exec`: routing, reversing each destination with `moveR`, merging and a final
  `moveR` restore every register, in `12 * (nb * B) + 14 * nb + 2 * nd + 9` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

set_option linter.unusedSimpArgs false

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {nd : ℕ}

/-! ### Block lists -/

section Blocks

variable {α : Type}

/-- The blocks of `l`, numbered from `n` (block `i` of `l` is `(l.drop (i * B)).take B` and has
index `n + i`), among the first `m`, whose counter value `(n + i) % W` selects `d`, concatenated
in increasing order. -/
def blocksAt (l : List α) (B W : ℕ) (sel : ℕ → Fin nd) (d : Fin nd) (n m : ℕ) : List α :=
  ((List.range m).filter (fun i => sel ((n + i) % W) = d)).flatMap
    (fun i => (l.drop (i * B)).take B)

/-- The blocks of `l` routed to `d`: the concatenation, in increasing block index `n < nb`, of the
blocks `(l.drop (n * B)).take B` with `sel (n % W) = d`. -/
def blocksTo (l : List α) (B W nb : ℕ) (sel : ℕ → Fin nd) (d : Fin nd) : List α :=
  ((List.range nb).filter (fun n => sel (n % W) = d)).flatMap (fun n => (l.drop (n * B)).take B)

lemma blocksTo_eq (l : List α) (B W nb : ℕ) (sel : ℕ → Fin nd) (d : Fin nd) :
    blocksTo l B W nb sel d = blocksAt l B W sel d 0 nb := by
  simp [blocksTo, blocksAt]

lemma blocksAt_zero (l : List α) (B W : ℕ) (sel : ℕ → Fin nd) (d : Fin nd) (n : ℕ) :
    blocksAt l B W sel d n 0 = [] := by simp [blocksAt]

lemma blocksAt_succ (l : List α) (B W : ℕ) (sel : ℕ → Fin nd) (d : Fin nd) (n m : ℕ) :
    blocksAt l B W sel d n (m + 1) =
      (if sel (n % W) = d then l.take B else []) ++ blocksAt (l.drop B) B W sel d (n + 1) m := by
  have hrest : (((List.range m).map Nat.succ).filter (fun i => sel ((n + i) % W) = d)).flatMap
      (fun i => (l.drop (i * B)).take B) = blocksAt (l.drop B) B W sel d (n + 1) m := by
    rw [List.filter_map, List.flatMap_map, blocksAt]
    have hp : ((fun i => decide (sel ((n + i) % W) = d)) ∘ Nat.succ) =
        fun i => decide (sel ((n + 1 + i) % W) = d) := by
      funext i
      simp only [Function.comp_apply, Nat.succ_eq_add_one, show n + (i + 1) = n + 1 + i by omega]
    have hg : (fun i => (l.drop (Nat.succ i * B)).take B) =
        fun i => ((l.drop B).drop (i * B)).take B := by
      funext i
      simp only [Nat.succ_eq_add_one, List.drop_drop, Nat.add_one_mul, Nat.add_comm (i * B) B]
    rw [hp, hg]
  rw [blocksAt, List.range_succ_eq_map, List.filter_cons]
  by_cases h : sel (n % W) = d
  · simp [h, hrest]
  · simp [h, hrest]

end Blocks

/-! ### Counter and dispatch -/

/-- The block counter after `x`: `x + 1`, wrapping to `0` at `W`. -/
def nextC (W : ℕ) (x : Fin (A + 4)) : Fin (A + 4) := if x.val + 1 < W then x + 1 else 0

/-- The counter tracks the block index modulo `W`. -/
lemma nextC_val {W n : ℕ} (hW1 : 1 ≤ W) (hW : W ≤ A + 4) {x : Fin (A + 4)} (hx : x.val = n % W) :
    (nextC W x).val = (n + 1) % W := by
  have hr : n % W < W := Nat.mod_lt _ (by omega)
  have hn : (n + 1) % W = (n % W + 1) % W := by
    conv_lhs => rw [← Nat.mod_add_div n W]
    rw [show n % W + W * (n / W) + 1 = (n % W + 1) + W * (n / W) by ring, Nat.add_mul_mod_self_left]
  unfold nextC
  split_ifs with h
  · rw [Fin.val_add, Fin.val_one, hn, Nat.mod_eq_of_lt (by omega : x.val + 1 < A + 4),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [hn, show n % W + 1 = W by omega, Nat.mod_self]; rfl

/-- Run `f d` for `d = sel (scan cs).val`, selected by a chain of branches over
`List.finRange nd`; the fallback `fb` is never reached. -/
def selDispatch (cs : Fin T) (sel : ℕ → Fin nd) (f : Fin nd → Act T Q A U) (fb : Act T Q A U) :
    Act T Q A U :=
  (List.finRange nd).foldr
    (fun d acc => .branch (fun v => decide (sel (v.scan cs).val = d)) (f d) acc) fb

lemma selDispatch_run (cs : Fin T) (sel : ℕ → Fin nd) (f : Fin nd → Act T Q A U) (fb : Act T Q A U)
    (s : Store (HΓ (T := T) A) (HS T Q A U)) :
    (selDispatch cs sel f fb).run s = (f (sel (s.var.scan cs).val)).run s := by
  have key : ∀ l : List (Fin nd), sel (s.var.scan cs).val ∈ l →
      (l.foldr (fun d acc => Action.branch (fun v => decide (sel (v.scan cs).val = d)) (f d) acc)
        fb).run s = (f (sel (s.var.scan cs).val)).run s := by
    intro l
    induction l with
    | nil => intro h; simp at h
    | cons d rest ih =>
        intro h
        simp only [List.foldr_cons, Action.run]
        by_cases hd : sel (s.var.scan cs).val = d
        · simp [hd]
        · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact ih (by simpa [hd] using h)
  exact key _ (List.mem_finRange _)

/-! ### Moving a register back, keeping the scratch slots -/

/-- `moveR_loop`, also keeping the scan slots. -/
theorem moveR_loop_scan (i j : Fin T) (hij : i ≠ j) (f : Fin (A + 4) → Fin (A + 4)) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R i = l → v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧ v'.scan = v.scan ∧
        Exec body (.loop (·.flag) (.act (moveStep i j f))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := movedR S.R i j f l }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, rfl, ?_⟩
      have : ({ S with R := movedR S.R i j f [] } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = j
          · subst hk; simp [movedR]
          · by_cases hk' : k = i
            · subst hk'; simp [movedR, hk, hS]
            · simp [movedR, hk, hk']
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hu, hsc, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update S.R i rest) j (f e :: S.R j) }
        (by simp [Function.update_of_ne hij]) rfl
      refine ⟨v', hu, hsc, ?_⟩
      have hrun : (moveStep i j f : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with R := Function.update (Function.update S.R i rest) j (f e :: S.R j) } := by
        simp [moveStep, peekR, Action.run, hS, update_rt, Function.update_of_ne hij,
          Function.update_of_ne hij.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (moveStep i j f) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = j
      · subst hk; simp [movedR, Function.update_of_ne hij.symm]
      · by_cases hk' : k = i
        · subst hk'; simp [movedR, hk]
        · simp [movedR, hk, hk']

/-- `moveR_exec`, also keeping the scan slots (the block counter lives there). -/
theorem moveR_exec_scan (i j : Fin T) (hij : i ≠ j) (f : Fin (A + 4) → Fin (A + 4))
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧ v'.scan = v.scan ∧
      Exec body (moveR i j f) (mk v S) (2 * (S.R i).length + 2)
        (mk v' { S with R := movedR S.R i j f (S.R i) }) := by
  obtain ⟨v', hu, hsc, he⟩ := moveR_loop_scan body i j hij f (S.R i)
    { v with flag := (S.R i).head?.isSome } S rfl rfl
  exact ⟨v', hu, hsc, Exec.cast (Exec.seq (peekR_run i v S ▸ Exec.act (body := body) (peekR i)
    (mk v S)) he) (by ring) rfl⟩

/-! ### Transferring one block -/

/-- One symbol of a block: move a counter symbol from `ctr` to `tmp`; then, for
`d = sel (scan cs).val`, pop `src d` and push the symbol onto `dst d`; record in `flag` whether
`ctr` is nonempty. -/
def xferStep (src dst : Fin nd → Fin T) (ctr tmp cs : Fin T) (sel : ℕ → Fin nd) : Act T Q A U :=
  .pop (.rt ctr) (fun v o => { v with sym := o })
    (.push (.rt tmp) (fun v => v.sym.getD blank)
      (selDispatch cs sel
        (fun d => .pop (.rt (src d)) (fun v o => { v with sym := o })
          (.push (.rt (dst d)) (fun v => v.sym.getD blank) (peekR ctr)))
        (peekR ctr)))

lemma xferStep_run (src dst : Fin nd → Fin T) (ctr tmp cs : Fin T) (sel : ℕ → Fin nd)
    (d : Fin nd) (h1 : src d ≠ ctr) (h2 : src d ≠ tmp) (h3 : ctr ≠ tmp) (h4 : dst d ≠ src d)
    (h5 : dst d ≠ ctr) (h6 : dst d ≠ tmp) (e x : Fin (A + 4)) (c₁ ys : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A) (hc : S.R ctr = e :: c₁) (hs : S.R (src d) = x :: ys)
    (hsel : sel (v.scan cs).val = d) :
    (xferStep src dst ctr tmp cs sel : Act T Q A U).run (mk v S) =
      mk { v with sym := some x, flag := c₁.head?.isSome } { S with
        R := Function.update (Function.update (Function.update (Function.update S.R ctr c₁) tmp
          (e :: S.R tmp)) (src d) ys) (dst d) (x :: S.R (dst d)) } := by
  simp [xferStep, peekR, Action.run, selDispatch_run, hc, hs, hsel, update_rt,
    Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
    Function.update_of_ne h1.symm, Function.update_of_ne h2.symm, Function.update_of_ne h3.symm,
    Function.update_of_ne h4.symm, Function.update_of_ne h5.symm, Function.update_of_ne h6.symm]

/-- The symbol loop of one block: it empties `ctr` onto `tmp` and moves `|ctr|` symbols from
`src d` to `dst d`, where `d` is the destination selected by the counter. -/
theorem xferStep_loop (src dst : Fin nd → Fin T) (ctr tmp cs : Fin T) (sel : ℕ → Fin nd)
    (d : Fin nd) (h1 : src d ≠ ctr) (h2 : src d ≠ tmp) (h3 : ctr ≠ tmp) (h4 : dst d ≠ src d)
    (h5 : dst d ≠ ctr) (h6 : dst d ≠ tmp) :
    ∀ (c₁ ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      c₁.length = ys.length → S.R ctr = c₁ → S.R (src d) = ys ++ rest →
      v.flag = c₁.head?.isSome → sel (v.scan cs).val = d →
      ∃ v' R', v'.user = v.user ∧ v'.scan = v.scan ∧
        Exec body (.loop (·.flag) (.act (xferStep src dst ctr tmp cs sel))) (mk v S)
          (2 * c₁.length + 1) (mk v' { S with R := R' }) ∧
        R' ctr = [] ∧ R' tmp = c₁.reverse ++ S.R tmp ∧ R' (src d) = rest ∧
        R' (dst d) = ys.reverse ++ S.R (dst d) ∧
        ∀ k, k ≠ src d → k ≠ ctr → k ≠ tmp → k ≠ dst d → R' k = S.R k := by
  intro c₁
  induction c₁ with
  | nil =>
      intro ys rest v S hlen hc hs hf _
      obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
      refine ⟨v, S.R, rfl, rfl, ?_, hc, rfl, by simpa using hs, rfl, fun _ _ _ _ _ => rfl⟩
      exact .loop_false (by simpa using hf)
  | cons e c₁ ih =>
      intro ys rest v S hlen hc hs hf hsel
      cases ys with
      | nil => simp at hlen
      | cons x ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        have hrun := xferStep_run src dst ctr tmp cs sel d h1 h2 h3 h4 h5 h6 e x c₁ (ys ++ rest) v S
          hc hs hsel
        obtain ⟨v', R', hu, hsc, he, hctr, htmp, hsrc, hdst, hoth⟩ := ih ys rest
          { v with sym := some x, flag := c₁.head?.isSome } { S with
            R := Function.update (Function.update (Function.update (Function.update S.R ctr c₁) tmp
              (e :: S.R tmp)) (src d) (ys ++ rest)) (dst d) (x :: S.R (dst d)) } hlen
          (by simp [Function.update_of_ne h1.symm, Function.update_of_ne h3,
            Function.update_of_ne h5.symm])
          (by simp [Function.update_of_ne h4.symm])
          rfl (by simpa using hsel)
        refine ⟨v', R', hu, hsc, ?_, hctr, ?_, hsrc, ?_, ?_⟩
        · exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
            (hrun ▸ Exec.act (body := body) _ (mk v S)) he) (by simp; ring) rfl
        · rw [htmp]
          simp [Function.update_of_ne h2.symm, Function.update_of_ne h6.symm,
            Function.update_of_ne h3.symm]
        · rw [hdst]
          simp
        · intro k hk1 hk2 hk3 hk4
          rw [hoth k hk1 hk2 hk3 hk4]
          simp [Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_of_ne hk3,
            Function.update_of_ne hk4]

/-- One block: transfer `|ctr|` symbols with `xferStep`, move `tmp` back onto `ctr`, advance the
block counter, then run `fin`. -/
def xferBlock (src dst : Fin nd → Fin T) (ctr tmp cs : Fin T) (W : ℕ) (sel : ℕ → Fin nd)
    (fin : Act T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR ctr))
    (.seq (.loop (·.flag) (.act (xferStep src dst ctr tmp cs sel)))
      (.seq (moveR tmp ctr id)
        (.act (.load (fun v => { v with scan := Function.update v.scan cs (nextC W (v.scan cs)) })
          fin))))

/-- One block, in `4 * |ctr| + 5` steps, ending with the action `fin`. -/
theorem xferBlock_exec (src dst : Fin nd → Fin T) (ctr tmp cs : Fin T) (W : ℕ)
    (sel : ℕ → Fin nd) (fin : Act T Q A U) (d : Fin nd) (h1 : src d ≠ ctr) (h2 : src d ≠ tmp)
    (h3 : ctr ≠ tmp) (h4 : dst d ≠ src d) (h5 : dst d ≠ ctr) (h6 : dst d ≠ tmp)
    (c ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hlen : c.length = ys.length) (hc : S.R ctr = c) (ht : S.R tmp = [])
    (hs : S.R (src d) = ys ++ rest) (hsel : sel (v.scan cs).val = d) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧ v'.scan = v.scan ∧
      Exec body (xferBlock src dst ctr tmp cs W sel fin) (mk v S) (4 * c.length + 5)
        (fin.run (mk { v' with scan := Function.update v.scan cs (nextC W (v.scan cs)) }
          { S with R := R' })) ∧
      R' ctr = c ∧ R' tmp = [] ∧ R' (src d) = rest ∧ R' (dst d) = ys.reverse ++ S.R (dst d) ∧
      ∀ k, k ≠ src d → k ≠ ctr → k ≠ tmp → k ≠ dst d → R' k = S.R k := by
  obtain ⟨v₁, R₁, hu₁, hsc₁, he₁, hctr₁, htmp₁, hsrc₁, hdst₁, hoth₁⟩ :=
    xferStep_loop body src dst ctr tmp cs sel d h1 h2 h3 h4 h5 h6 c ys rest
      { v with flag := c.head?.isSome } S hlen hc hs rfl hsel
  obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := moveR_exec_scan body tmp ctr h3.symm id v₁ { S with R := R₁ }
  have he₀ := Exec.act (body := body) (peekR ctr) (mk v S)
  rw [peekR_run, hc] at he₀
  have he₃ := Exec.act (body := body)
    (.load (fun v => { v with scan := Function.update v.scan cs (nextC W (v.scan cs)) }) fin)
    (mk v₂ { S with R := movedR R₁ tmp ctr id (R₁ tmp) })
  have hv₂ : v₂.scan = v.scan := by rw [hsc₂, hsc₁]
  refine ⟨v₂, movedR R₁ tmp ctr id (R₁ tmp), by rw [hu₂, hu₁], hv₂,
    Exec.cast (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ he₃))) ?_ ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [htmp₁, ht]; ring
  · simp [Action.run, hv₂]
  · simp [movedR, htmp₁, ht, hctr₁]
  · simp [movedR, Function.update_of_ne h3.symm]
  · simp [movedR, h1, h2, hsrc₁]
  · simp [movedR, h5, h6, hdst₁]
  · intro k hk1 hk2 hk3 hk4
    simp [movedR, hk2, hk3, hoth₁ k hk1 hk2 hk3 hk4]


/-! ### Routing -/

/-- Reset the block counter to `0` and record in `flag` whether register `i` is nonempty. -/
def initCounter (cs i : Fin T) : Act T Q A U :=
  .load (fun v => { v with scan := Function.update v.scan cs 0 }) (peekR i)

/-- Route the stream in `src` block by block: block `n` (of `|ctr|` symbols) goes onto
`dst (sel (n % W))`. The loop runs while `src` is nonempty. -/
def routeBlocks (src : Fin T) (dst : Fin nd → Fin T) (ctr tmp cs : Fin T) (W : ℕ)
    (sel : ℕ → Fin nd) : Pr P T Q A U :=
  .seq (.act (initCounter cs src))
    (.loop (·.flag) (xferBlock (fun _ => src) dst ctr tmp cs W sel (peekR src)))

/-- The block loop of `routeBlocks`, from block index `n` with `m` blocks left. -/
theorem routeBlocks_loop (src : Fin T) (dst : Fin nd → Fin T) (ctr tmp cs : Fin T) (W : ℕ)
    (sel : ℕ → Fin nd) (hW1 : 1 ≤ W) (hW : W ≤ A + 4) (h1 : src ≠ ctr) (h2 : src ≠ tmp)
    (h3 : ctr ≠ tmp) (h4 : ∀ d, dst d ≠ src) (h5 : ∀ d, dst d ≠ ctr) (h6 : ∀ d, dst d ≠ tmp)
    (hinj : Function.Injective dst) {B : ℕ} (hB : 1 ≤ B) (c : List (Fin (A + 4)))
    (hcB : c.length = B) :
    ∀ (m n : ℕ) (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      l.length = m * B → S.R src = l → S.R ctr = c → S.R tmp = [] → (v.scan cs).val = n % W →
      v.flag = l.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (.loop (·.flag) (xferBlock (fun _ => src) dst ctr tmp cs W sel (peekR src)))
          (mk v S) (m * (4 * B + 6) + 1) (mk v' { S with R := R' }) ∧
        R' src = [] ∧ R' ctr = c ∧ R' tmp = [] ∧
        (∀ d, R' (dst d) = (blocksAt l B W sel d n m).reverse ++ S.R (dst d)) ∧
        ∀ k, k ≠ src → k ≠ ctr → k ≠ tmp → (∀ d, dst d ≠ k) → R' k = S.R k := by
  intro m
  induction m with
  | zero =>
      intro n l v S hl hs hc ht _ hf
      obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      exact ⟨v, S.R, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) rfl, hs, hc, ht,
        fun d => by simp [blocksAt_zero], fun _ _ _ _ _ => rfl⟩
  | succ m ih =>
      intro n l v S hl hs hc ht hx hf
      have hlB : B ≤ l.length := by rw [hl]; nlinarith
      obtain ⟨v₁, R₁, hu₁, hsc₁, he₁, hctr₁, htmp₁, hsrc₁, hdst₁, hoth₁⟩ :=
        xferBlock_exec body (fun _ => src) dst ctr tmp cs W sel (peekR src) (sel (n % W)) h1 h2 h3
          (h4 _) (h5 _) (h6 _) c (l.take B) (l.drop B) v S (by simp [hcB]; omega) hc ht
          (by simp [hs]) (by rw [hx])
      rw [peekR_run] at he₁
      obtain ⟨v', R', hu, he, hsrc, hctr, htmp, hdst, hoth⟩ := ih (n + 1) (l.drop B)
        { v₁ with scan := Function.update v.scan cs (nextC W (v.scan cs)),
                  flag := (R₁ src).head?.isSome }
        { S with R := R₁ } (by simp [hl, Nat.add_one_mul]) hsrc₁ hctr₁ htmp₁
        (by simp [nextC_val hW1 hW hx]) (by simp [hsrc₁])
      have hne : l ≠ [] := by
        intro h; rw [h] at hlB; simp at hlB; omega
      refine ⟨v', R', by rw [hu, hu₁], Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
        (by simpa [hf] using hne) he₁ he) (by rw [hcB]; ring) rfl, hsrc, hctr, htmp, ?_, ?_⟩
      · intro d
        rw [hdst, blocksAt_succ]
        dsimp only
        by_cases hd : sel (n % W) = d
        · subst hd
          simp [hdst₁]
        · rw [hoth₁ (dst d) (h4 d) (h5 d) (h6 d) (fun h => hd (hinj h).symm)]
          simp [hd]
      · intro k hk1 hk2 hk3 hk4
        exact (hoth k hk1 hk2 hk3 hk4).trans (hoth₁ k hk1 hk2 hk3 (fun h => hk4 _ h.symm))

/-- Routing a stream of `nb` blocks of `B ≥ 1` symbols: `dst d` receives the reversal of
`blocksTo l B W nb sel d`; `src` ends empty, `ctr` and `tmp` are restored, every other stack
is unchanged. Exactly `4 * (nb * B) + 6 * nb + 2` steps. -/
theorem routeBlocks_exec (src : Fin T) (dst : Fin nd → Fin T) (ctr tmp cs : Fin T) (W : ℕ)
    (sel : ℕ → Fin nd) (hW1 : 1 ≤ W) (hW : W ≤ A + 4) (hreg : [src, ctr, tmp].Nodup)
    (hdst : ∀ d, dst d ∉ [src, ctr, tmp]) (hinj : Function.Injective dst)
    {l c : List (Fin (A + 4))} {nb B : ℕ} (hB : 1 ≤ B) (hl : l.length = nb * B)
    (hcB : c.length = B) (v : HS T Q A U) (S : Stacks T A) (hs : S.R src = l) (hc : S.R ctr = c)
    (ht : S.R tmp = []) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ 4 * (nb * B) + 6 * nb + 2 ∧
      Exec body (routeBlocks src dst ctr tmp cs W sel) (mk v S) m (mk v' { S with R := R' }) ∧
      R' src = [] ∧ R' ctr = c ∧ R' tmp = [] ∧
      (∀ d, R' (dst d) = (blocksTo l B W nb sel d).reverse ++ S.R (dst d)) ∧
      ∀ k, k ∉ [src, ctr, tmp] → (∀ d, dst d ≠ k) → R' k = S.R k := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg hdst
  obtain ⟨⟨h1, h2⟩, h3⟩ := hreg
  have he₀ := Exec.act (body := body) (initCounter cs src) (mk v S)
  have hrun : (initCounter cs src : Act T Q A U).run (mk v S) =
      mk { v with scan := Function.update v.scan cs 0, flag := (S.R src).head?.isSome } S := rfl
  rw [hrun] at he₀
  obtain ⟨v', R', hu, he, hsrc, hctr, htmp, hd, hoth⟩ :=
    routeBlocks_loop body src dst ctr tmp cs W sel hW1 hW h1 h2 h3 (fun d => (hdst d).1)
      (fun d => (hdst d).2.1) (fun d => (hdst d).2.2) hinj hB c hcB nb 0 l
      { v with scan := Function.update v.scan cs 0, flag := (S.R src).head?.isSome } S hl hs hc ht
      (by simp) (by simp [hs])
  refine ⟨v', R', _, hu, le_of_eq (by ring), Exec.seq he₀ he, hsrc, hctr, htmp,
    fun d => by rw [hd, blocksTo_eq], fun k hk hk' => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
  exact hoth k hk.1 hk.2.1 hk.2.2 hk'


/-! ### Merging -/

/-- Merge blocks into `dst`: for each symbol of `cnt`, with block index `n = 0, 1, …`, pop one
block of `|ctr|` symbols from `srcs (sel (n % W))` and push it onto `dst`. Each block moves one
symbol of `cnt` onto `ctmp`; a final `moveR` moves `ctmp` back onto `cnt`. -/
def mergeBlocks (srcs : Fin nd → Fin T) (dst ctr tmp cs cnt ctmp : Fin T) (W : ℕ)
    (sel : ℕ → Fin nd) : Pr P T Q A U :=
  .seq (.act (initCounter cs cnt))
    (.seq (.loop (·.flag) (xferBlock srcs (fun _ => dst) ctr tmp cs W sel (moveStep cnt ctmp id)))
      (moveR ctmp cnt id))

/-- The block loop of `mergeBlocks`, from block index `n` with the blocks left counted by `kk`. -/
theorem mergeBlocks_loop (srcs : Fin nd → Fin T) (dst ctr tmp cs cnt ctmp : Fin T) (W : ℕ)
    (sel : ℕ → Fin nd) (hW1 : 1 ≤ W) (hW : W ≤ A + 4) (h1 : ∀ d, srcs d ≠ ctr)
    (h2 : ∀ d, srcs d ≠ tmp) (h3 : ctr ≠ tmp) (h4 : ∀ d, dst ≠ srcs d) (h5 : dst ≠ ctr)
    (h6 : dst ≠ tmp) (h7 : ∀ d, srcs d ≠ cnt) (h8 : ∀ d, srcs d ≠ ctmp) (h9 : dst ≠ cnt)
    (h10 : dst ≠ ctmp) (h11 : ctr ≠ cnt) (h12 : ctr ≠ ctmp) (h13 : tmp ≠ cnt) (h14 : tmp ≠ ctmp)
    (h15 : cnt ≠ ctmp) (hinj : Function.Injective srcs) {B : ℕ} (c : List (Fin (A + 4)))
    (hcB : c.length = B) (rest : Fin nd → List (Fin (A + 4))) :
    ∀ (kk : List (Fin (A + 4))) (n : ℕ) (l : List (Fin (A + 4))) (v : HS T Q A U)
      (S : Stacks T A),
      S.R cnt = kk → l.length = kk.length * B →
      (∀ d, S.R (srcs d) = blocksAt l B W sel d n kk.length ++ rest d) →
      S.R ctr = c → S.R tmp = [] → (v.scan cs).val = n % W → v.flag = kk.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body
          (.loop (·.flag) (xferBlock srcs (fun _ => dst) ctr tmp cs W sel (moveStep cnt ctmp id)))
          (mk v S) (kk.length * (4 * B + 6) + 1) (mk v' { S with R := R' }) ∧
        R' cnt = [] ∧ R' ctmp = kk.reverse ++ S.R ctmp ∧ R' ctr = c ∧ R' tmp = [] ∧
        (∀ d, R' (srcs d) = rest d) ∧ R' dst = l.reverse ++ S.R dst ∧
        ∀ k, k ≠ dst → k ≠ ctr → k ≠ tmp → k ≠ cnt → k ≠ ctmp → (∀ d, srcs d ≠ k) →
          R' k = S.R k := by
  intro kk
  induction kk with
  | nil =>
      intro n l v S hk hl hs hc ht _ hf
      obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      exact ⟨v, S.R, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) rfl, hk, rfl, hc,
        ht, fun d => by simpa [blocksAt_zero] using hs d, by simp, fun _ _ _ _ _ _ _ => rfl⟩
  | cons e kk ih =>
      intro n l v S hk hl hs hc ht hx hf
      have hlB : B ≤ l.length := by rw [hl]; simp; nlinarith
      obtain ⟨d₀, hd₀⟩ : ∃ d₀, sel (n % W) = d₀ := ⟨_, rfl⟩
      obtain ⟨v₁, R₁, hu₁, hsc₁, he₁, hctr₁, htmp₁, hsrc₁, hdst₁, hoth₁⟩ :=
        xferBlock_exec body srcs (fun _ => dst) ctr tmp cs W sel (moveStep cnt ctmp id) d₀
          (h1 _) (h2 _) h3 (h4 _) h5 h6 c (l.take B)
          (blocksAt (l.drop B) B W sel d₀ (n + 1) kk.length ++ rest d₀) v S
          (by simp [hcB]; omega) hc ht
          (by rw [hs d₀, List.length_cons, blocksAt_succ]; simp [hd₀])
          (by rw [hx, hd₀])
      have hcnt₁ : R₁ cnt = e :: kk := by
        rw [hoth₁ cnt (h7 _).symm h11.symm h13.symm h9.symm, hk]
      have hct₁ : R₁ ctmp = S.R ctmp := hoth₁ ctmp (h8 _).symm h12.symm h14.symm h10.symm
      have hrun : (moveStep cnt ctmp id : Act T Q A U).run
          (mk { v₁ with scan := Function.update v.scan cs (nextC W (v.scan cs)) }
            { S with R := R₁ }) =
          mk { v₁ with
                scan := Function.update v.scan cs (nextC W (v.scan cs))
                sym := some e
                flag := kk.head?.isSome }
            { S with R := Function.update (Function.update R₁ cnt kk) ctmp (e :: R₁ ctmp) } := by
        simp [moveStep, peekR, Action.run, hcnt₁, update_rt, Function.update_of_ne h15,
          Function.update_of_ne h15.symm]
      rw [hrun] at he₁
      obtain ⟨v', R', hu, he, hcnt, hct, hctr, htmp, hsrc, hdst, hoth⟩ := ih (n + 1) (l.drop B)
        { v₁ with
          scan := Function.update v.scan cs (nextC W (v.scan cs))
          sym := some e
          flag := kk.head?.isSome }
        { S with R := Function.update (Function.update R₁ cnt kk) ctmp (e :: R₁ ctmp) }
        (by simp [Function.update_of_ne h15])
        (by simp [hl, Nat.add_one_mul])
        (by
          intro d
          simp only [Function.update_of_ne (h7 d), Function.update_of_ne (h8 d)]
          by_cases hd : d₀ = d
          · subst hd; exact hsrc₁
          · rw [hoth₁ (srcs d) (fun h => hd (hinj h).symm) (h1 d) (h2 d) (h4 d).symm, hs d,
              List.length_cons, blocksAt_succ]
            simp [hd₀, hd])
        (by simp [Function.update_of_ne h11, Function.update_of_ne h12, hctr₁])
        (by simp [Function.update_of_ne h13, Function.update_of_ne h14, htmp₁])
        (by simp [nextC_val hW1 hW hx]) rfl
      refine ⟨v', R', by rw [hu, hu₁], Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
        (by simpa using hf) he₁ he) (by simp [hcB]; ring) rfl, hcnt, ?_, hctr, htmp, hsrc, ?_, ?_⟩
      · rw [hct]; simp [hct₁]
      · rw [hdst]
        simp [Function.update_of_ne h9, Function.update_of_ne h10, hdst₁]
        rw [← List.append_assoc, ← List.reverse_append, List.take_append_drop]
      · intro k hk1 hk2 hk3 hk4 hk5 hk6
        refine (hoth k hk1 hk2 hk3 hk4 hk5 hk6).trans ?_
        simp only [Function.update_of_ne hk4, Function.update_of_ne hk5]
        exact hoth₁ k (fun h => hk6 _ h.symm) hk2 hk3 hk1

/-- Merging `nb` blocks of `B` symbols (`nb` is the length of `cnt`): if each source `srcs d`
holds `blocksTo l B W nb sel d` on top of a remainder `rest d`, then `dst` receives the reversal
of `l`, each source is left with its remainder, `ctr`, `tmp`, `cnt` and `ctmp` are restored, and
every other stack is unchanged. Exactly `4 * (nb * B) + 8 * nb + 4` steps. -/
theorem mergeBlocks_exec (srcs : Fin nd → Fin T) (dst ctr tmp cs cnt ctmp : Fin T) (W : ℕ)
    (sel : ℕ → Fin nd) (hW1 : 1 ≤ W) (hW : W ≤ A + 4) (hreg : [dst, ctr, tmp, cnt, ctmp].Nodup)
    (hsrcs : ∀ d, srcs d ∉ [dst, ctr, tmp, cnt, ctmp]) (hinj : Function.Injective srcs)
    {l c kk : List (Fin (A + 4))} {nb B : ℕ} (hl : l.length = nb * B) (hcB : c.length = B)
    (hk : kk.length = nb) (rest : Fin nd → List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hs : ∀ d, S.R (srcs d) = blocksTo l B W nb sel d ++ rest d) (hc : S.R ctr = c)
    (ht : S.R tmp = []) (hcnt : S.R cnt = kk) (hct : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ 4 * (nb * B) + 8 * nb + 4 ∧
      Exec body (mergeBlocks srcs dst ctr tmp cs cnt ctmp W sel) (mk v S) m
        (mk v' { S with R := R' }) ∧
      R' dst = l.reverse ++ S.R dst ∧ (∀ d, R' (srcs d) = rest d) ∧
      R' ctr = c ∧ R' tmp = [] ∧ R' cnt = kk ∧ R' ctmp = [] ∧
      ∀ k, k ∉ [dst, ctr, tmp, cnt, ctmp] → (∀ d, srcs d ≠ k) → R' k = S.R k := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg hsrcs
  obtain ⟨⟨h5, h6, h9, h10⟩, ⟨h3, h11, h12⟩, ⟨h13, h14⟩, h15⟩ := hreg
  have he₀ := Exec.act (body := body) (initCounter cs cnt) (mk v S)
  have hrun : (initCounter cs cnt : Act T Q A U).run (mk v S) =
      mk { v with scan := Function.update v.scan cs 0, flag := (S.R cnt).head?.isSome } S := rfl
  rw [hrun] at he₀
  obtain ⟨v₁, R₁, hu₁, he₁, hcnt₁, hct₁, hctr₁, htmp₁, hsrc₁, hdst₁, hoth₁⟩ :=
    mergeBlocks_loop body srcs dst ctr tmp cs cnt ctmp W sel hW1 hW (fun d => (hsrcs d).2.1)
      (fun d => (hsrcs d).2.2.1) h3 (fun d => Ne.symm (hsrcs d).1) h5 h6
      (fun d => (hsrcs d).2.2.2.1) (fun d => (hsrcs d).2.2.2.2) h9 h10 h11 h12 h13 h14 h15 hinj
      c hcB rest kk 0 l
      { v with scan := Function.update v.scan cs 0, flag := (S.R cnt).head?.isSome } S hcnt
      (by rw [hl, hk]) (fun d => by rw [hs d, blocksTo_eq, hk]) hc ht (by simp) (by simp [hcnt])
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body ctmp cnt (Ne.symm h15) id v₁ { S with R := R₁ }
  refine ⟨v₂, movedR R₁ ctmp cnt id (R₁ ctmp), _, by rw [hu₂, hu₁], le_of_eq ?_,
    Exec.seq he₀ (Exec.seq he₁ he₂), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hct₁, hct, hk]; ring
  · simp [movedR, h9, h10, hdst₁]
  · intro d; simp [movedR, (hsrcs d).2.2.2.1, (hsrcs d).2.2.2.2, hsrc₁]
  · simp [movedR, h11, h12, hctr₁]
  · simp [movedR, h13, h14, htmp₁]
  · simp [movedR, hct₁, hct, hcnt₁]
  · simp [movedR, Function.update_of_ne (Ne.symm h15)]
  · intro k hk hk'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    obtain ⟨hk1, hk2, hk3, hk4, hk5⟩ := hk
    simp [movedR, hk4, hk5, hoth₁ k hk1 hk2 hk3 hk4 hk5 hk']


/-! ### Round trip -/

/-- The routed block lists partition the first `m` blocks. -/
lemma sum_blocksAt_length {α : Type} (B W : ℕ) (sel : ℕ → Fin nd) :
    ∀ (m n : ℕ) (l : List α), l.length = m * B →
      ∑ d : Fin nd, (blocksAt l B W sel d n m).length = m * B := by
  intro m
  induction m with
  | zero => intro n l _; simp [blocksAt_zero]
  | succ m ih =>
      intro n l hl
      simp only [blocksAt_succ, List.length_append]
      rw [Finset.sum_add_distrib, ih (n + 1) (l.drop B) (by simp [hl, Nat.add_one_mul])]
      have hB : B ≤ l.length := by rw [hl]; nlinarith
      have : ∑ d : Fin nd, (if sel (n % W) = d then l.take B else []).length = B := by
        simp only [apply_ite List.length, List.length_nil]
        rw [Finset.sum_ite_eq]
        simp [hB]
      rw [this]; ring

/-- Reverse each `dst d` onto `aux d`, for `d` in a duplicate-free list. -/
theorem revList_exec (dst aux : Fin nd → Fin T) (hda : ∀ d d', dst d ≠ aux d')
    (hdinj : Function.Injective dst) (hainj : Function.Injective aux) :
    ∀ (ds : List (Fin nd)), ds.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (Prog.seqList (ds.map fun d => moveR (dst d) (aux d) id)) (mk v S)
          ((ds.map fun d => 2 * (S.R (dst d)).length + 2).sum + 1) (mk v' { S with R := R' }) ∧
        (∀ d ∈ ds, R' (dst d) = [] ∧ R' (aux d) = (S.R (dst d)).reverse ++ S.R (aux d)) ∧
        ∀ k, (∀ d ∈ ds, k ≠ dst d ∧ k ≠ aux d) → R' k = S.R k := by
  intro ds
  induction ds with
  | nil =>
      intro _ v S
      exact ⟨v, S.R, rfl, by simpa [Prog.seqList] using Exec.act (body := body) .done (mk v S),
        by simp, fun _ _ => rfl⟩
  | cons d ds ih =>
      intro hnd v S
      rw [List.nodup_cons] at hnd
      obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body (dst d) (aux d) (hda d d) id v S
      obtain ⟨v', R', hu, he, hds, hoth⟩ := ih hnd.2 v₁
        { S with R := movedR S.R (dst d) (aux d) id (S.R (dst d)) }
      have hfr : ∀ d' ∈ ds, movedR S.R (dst d) (aux d) id (S.R (dst d)) (dst d') = S.R (dst d') ∧
          movedR S.R (dst d) (aux d) id (S.R (dst d)) (aux d') = S.R (aux d') := by
        intro d' hd'
        have hne : d' ≠ d := fun h => hnd.1 (h ▸ hd')
        refine ⟨?_, ?_⟩
        · simp [movedR, Function.update_of_ne (hda d' d),
            Function.update_of_ne (fun h => hne (hdinj h))]
        · simp [movedR, Function.update_of_ne (fun h => hne (hainj h)),
            Function.update_of_ne (hda d d').symm]
      refine ⟨v', R', by rw [hu, hu₁], Exec.cast (Exec.seq he₁ he) ?_ rfl, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        rw [List.map_congr_left (fun d' hd' => by rw [(hfr d' hd').1])]
        ring
      · intro d' hd'
        rcases List.mem_cons.1 hd' with rfl | hd'
        · have hk : ∀ d'' ∈ ds, dst d' ≠ dst d'' ∧ dst d' ≠ aux d'' := fun d'' hd'' =>
            ⟨fun h => hnd.1 (hdinj h ▸ hd''), hda _ _⟩
          have hk' : ∀ d'' ∈ ds, aux d' ≠ dst d'' ∧ aux d' ≠ aux d'' := fun d'' hd'' =>
            ⟨(hda _ _).symm, fun h => hnd.1 (hainj h ▸ hd'')⟩
          rw [hoth _ hk, hoth _ hk']
          simp [movedR, hda d' d']
        · refine ⟨(hds d' hd').1, ?_⟩
          rw [(hds d' hd').2]
          dsimp only
          rw [(hfr d' hd').1, (hfr d' hd').2]
      · intro k hk
        rw [hoth k (fun d' hd' => hk d' (List.mem_cons_of_mem _ hd'))]
        have := hk d List.mem_cons_self
        simp [movedR, Function.update_of_ne this.1, Function.update_of_ne this.2]

/-- Reverse each `dst d` onto `aux d`. -/
def revEach (dst aux : Fin nd → Fin T) : Pr P T Q A U :=
  Prog.seqList ((List.finRange nd).map fun d => moveR (dst d) (aux d) id)

/-- Route `src` onto the registers `dst d`, reverse each of them onto `aux d`, merge the `aux d`
into `out` with the same selector, and move `out` back onto `src`. -/
def roundTrip (src : Fin T) (dst aux : Fin nd → Fin T) (ctr tmp cs cnt ctmp out : Fin T) (W : ℕ)
    (sel : ℕ → Fin nd) : Pr P T Q A U :=
  .seq (routeBlocks src dst ctr tmp cs W sel)
    (.seq (revEach dst aux)
      (.seq (mergeBlocks aux out ctr tmp cs cnt ctmp W sel) (moveR out src id)))


/-- The round trip restores every register: from a store with the stream `l` of `nb` blocks of
`B ≥ 1` symbols in `src`, `B` symbols in `ctr`, `nb` symbols in `cnt`, and `tmp`, `ctmp`, `out`,
every `dst d` and every `aux d` empty, `roundTrip` returns to the same stacks. -/
theorem roundTrip_exec (src : Fin T) (dst aux : Fin nd → Fin T) (ctr tmp cs cnt ctmp out : Fin T)
    (W : ℕ) (sel : ℕ → Fin nd) (hW1 : 1 ≤ W) (hW : W ≤ A + 4)
    (hreg : [src, ctr, tmp, cnt, ctmp, out].Nodup)
    (hdst : ∀ d, dst d ∉ [src, ctr, tmp, cnt, ctmp, out])
    (haux : ∀ d, aux d ∉ [src, ctr, tmp, cnt, ctmp, out]) (hda : ∀ d d', dst d ≠ aux d')
    (hdinj : Function.Injective dst) (hainj : Function.Injective aux)
    {l c kk : List (Fin (A + 4))} {nb B : ℕ} (hB : 1 ≤ B) (hl : l.length = nb * B)
    (hcB : c.length = B) (hk : kk.length = nb) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = l) (hc : S.R ctr = c) (ht : S.R tmp = []) (hcnt : S.R cnt = kk)
    (hct : S.R ctmp = []) (hout : S.R out = []) (hd : ∀ d, S.R (dst d) = [])
    (ha : ∀ d, S.R (aux d) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 12 * (nb * B) + 14 * nb + 2 * nd + 9 ∧
      Exec body (roundTrip src dst aux ctr tmp cs cnt ctmp out W sel) (mk v S) m (mk v' S) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg hdst haux
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3⟩, ⟨d1, d2⟩, e1⟩ := hreg
  -- routing
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hsrc₁, hctr₁, htmp₁, hdst₁, hoth₁⟩ :=
    routeBlocks_exec body src dst ctr tmp cs W sel hW1 hW (by simp [a1, a2, b1])
      (fun d => by simp [(hdst d).1, (hdst d).2.1, (hdst d).2.2.1]) hdinj hB hl hcB v S hs hc ht
  have hfr₁ : ∀ k, k ≠ src → k ≠ ctr → k ≠ tmp → (∀ d, dst d ≠ k) → R₁ k = S.R k :=
    fun k h1 h2 h3 h4 => hoth₁ k (by simp [h1, h2, h3]) h4
  have hdst₁' : ∀ d, R₁ (dst d) = (blocksTo l B W nb sel d).reverse := fun d => by
    rw [hdst₁, hd]; simp
  -- reversing each destination
  obtain ⟨v₂, R₂, hu₂, he₂, hds₂, hoth₂⟩ := revList_exec body dst aux hda hdinj hainj
    (List.finRange nd) (List.nodup_finRange nd) v₁ { S with R := R₁ }
  have hfr₂ : ∀ k, (∀ d, k ≠ dst d ∧ k ≠ aux d) → R₂ k = R₁ k :=
    fun k hk => hoth₂ k (fun d _ => hk d)
  have haux₂ : ∀ d, R₂ (aux d) = blocksTo l B W nb sel d ++ [] := by
    intro d
    rw [(hds₂ d (List.mem_finRange d)).2]
    dsimp only
    rw [hdst₁', hfr₁ (aux d) (haux d).1 (haux d).2.1 (haux d).2.2.1 (fun d' => hda d' d), ha]
    simp
  have hsum : ((List.finRange nd).map fun d => 2 * (R₁ (dst d)).length + 2).sum =
      2 * (nb * B) + 2 * nd := by
    rw [← Fin.sum_univ_def]
    simp only [hdst₁', List.length_reverse, blocksTo_eq]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_blocksAt_length B W sel nb 0 l hl]
    simp [Nat.mul_comm]
  -- registers outside the routed family keep their contents through the first two stages
  have hkeep : ∀ k, k ≠ src → k ≠ ctr → k ≠ tmp → (∀ d, k ≠ dst d ∧ k ≠ aux d) →
      R₂ k = S.R k := fun k h1 h2 h3 h4 =>
    (hfr₂ k h4).trans (hfr₁ k h1 h2 h3 (fun d h => (h4 d).1 h.symm))
  have hne : ∀ k, k = cnt ∨ k = ctmp ∨ k = out → ∀ d, k ≠ dst d ∧ k ≠ aux d := by
    rintro k (rfl | rfl | rfl) d
    · exact ⟨fun h => (hdst d).2.2.2.1 h.symm, fun h => (haux d).2.2.2.1 h.symm⟩
    · exact ⟨fun h => (hdst d).2.2.2.2.1 h.symm, fun h => (haux d).2.2.2.2.1 h.symm⟩
    · exact ⟨fun h => (hdst d).2.2.2.2.2 h.symm, fun h => (haux d).2.2.2.2.2 h.symm⟩
  -- merging
  obtain ⟨v₃, R₃, m₃, hu₃, hm₃, he₃, hout₃, hsrc₃, hctr₃, htmp₃, hcnt₃, hct₃, hoth₃⟩ :=
    mergeBlocks_exec body aux out ctr tmp cs cnt ctmp W sel hW1 hW
      (by simp [b1, b2, b3, c1, c2, d1, Ne.symm b4, Ne.symm c3, Ne.symm d2, Ne.symm e1])
      (fun d => by
        obtain ⟨_, x2, x3, x4, x5, x6⟩ := haux d
        simp [x2, x3, x4, x5, x6])
      hainj hl hcB hk (fun _ => []) v₂ { S with R := R₂ } haux₂
      ((hfr₂ ctr (fun d => ⟨fun h => (hdst d).2.1 h.symm,
        fun h => (haux d).2.1 h.symm⟩)).trans hctr₁)
      ((hfr₂ tmp (fun d => ⟨fun h => (hdst d).2.2.1 h.symm,
        fun h => (haux d).2.2.1 h.symm⟩)).trans htmp₁)
      ((hkeep cnt (Ne.symm a3) (Ne.symm b2) (Ne.symm c1) (hne _ (Or.inl rfl))).trans hcnt)
      ((hkeep ctmp (Ne.symm a4) (Ne.symm b3) (Ne.symm c2) (hne _ (Or.inr (Or.inl rfl)))).trans
        hct)
  have hout₂ : R₂ out = [] := by
    rw [hkeep out (Ne.symm a5) (Ne.symm b4) (Ne.symm c3) (hne _ (Or.inr (Or.inr rfl)))]
    exact hout
  have hsrc₂ : R₂ src = [] := by
    rw [hfr₂ src (fun d => ⟨fun h => (hdst d).1 h.symm, fun h => (haux d).1 h.symm⟩)]
    exact hsrc₁
  have hout₃' : R₃ out = l.reverse := by rw [hout₃]; dsimp only; rw [hout₂]; simp
  have hsrc₃' : R₃ src = [] := by
    rw [hoth₃ src (by simp [a1, a2, a3, a4, a5]) (fun d h => (haux d).1 h)]
    exact hsrc₂
  -- moving the merged stream back
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body out src (Ne.symm a5) id v₃ { S with R := R₃ }
  have hfin : movedR R₃ out src id (R₃ out) = S.R := by
    funext k
    by_cases hk1 : k = src
    · subst hk1; simp [movedR, hout₃', hsrc₃', hs]
    by_cases hk2 : k = out
    · subst hk2; simp [movedR, Ne.symm a5, hout]
    simp only [movedR, Function.update_of_ne hk1, Function.update_of_ne hk2]
    by_cases hk3 : k = ctr
    · subst hk3; rw [hctr₃, hc]
    by_cases hk4 : k = tmp
    · subst hk4; rw [htmp₃, ht]
    by_cases hk5 : k = cnt
    · subst hk5; rw [hcnt₃, hcnt]
    by_cases hk6 : k = ctmp
    · subst hk6; rw [hct₃, hct]
    by_cases hk7 : ∃ d, aux d = k
    · obtain ⟨d, rfl⟩ := hk7; rw [hsrc₃, ha]
    simp only [not_exists] at hk7
    rw [hoth₃ k (by simp [hk1, hk2, hk3, hk4, hk5, hk6]) hk7]
    dsimp only
    by_cases hk8 : ∃ d, dst d = k
    · obtain ⟨d, rfl⟩ := hk8; rw [(hds₂ d (List.mem_finRange d)).1, hd]
    simp only [not_exists] at hk8
    exact hkeep k hk1 hk3 hk4 (fun d => ⟨fun h => hk8 d h.symm, fun h => hk7 d h.symm⟩)
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))) rfl ?_⟩
  · have hsum' : ((List.finRange nd).map fun d => 2 * ({ S with R := R₁ }.R (dst d)).length +
        2).sum = 2 * (nb * B) + 2 * nd := hsum
    have hlen : ({ S with R := R₃ }.R out).length = nb * B := by
      simp [hout₃', hl]
    rw [hsum', hlen]
    omega
  · simp only [hfin]

end IntegerMultBounds.MathlibTM2.Host
