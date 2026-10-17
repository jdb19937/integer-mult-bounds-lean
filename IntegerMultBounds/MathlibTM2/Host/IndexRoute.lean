module

public import IntegerMultBounds.MathlibTM2.Host.Index
public import IntegerMultBounds.MathlibTM2.Host.Route

/-!
# Routing and merging records by index code

Records are blocks of `B` symbols: record `n` of a stream `l` is `blk l B n`. Record `n` of a
stream started at index `i₀` has index `i₀ + n`, and its destination is the code of its index,
computed on the host by a code pass (`codePass`) over the field counter (`incrFields`) of
`IntegerMultBounds.MathlibTM2.Host.Index`.

Register interface, bundled in `IdxLayout cf len L rs tmps rsrc st X` with `X` the stream
registers of the program (`routeRegs`, `mergeRegs`):

* the fields `cf f` hold the digits of the current index (`IdxState`);
* the code-pass registers `rs r`: the field `cf f` (of length `L`) if `rsrc r = .inl f`, a
  parameter register holding `binSyms L p` if `rsrc r = .inr p`; the code of index `i` is
  `idxCode C L len rsrc i = C.eval L (regVal len rsrc i)`;
* the empty spare registers `tmps r`, and the scan slot `st` for the code and the carry;
* the record length is the length of a counter register `ctr`, with an empty spare `tmp`.

`routeIdx` loops while `src` is nonempty; `mergeIdx` runs one record per symbol of a count
register `cnt`, as `mergeBlocks` does. Each record (`idxStep`) is a code pass, one `xferBlock`
selected by the code, and an increment.

* `routeIdx_exec`: `dst d` gains `(blocksIdx l B nb code i₀ d).reverse`, in exactly
  `nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 13) + 2` steps;
* `mergeIdx_exec`: `dst` gains the reversal of the list semantics `mergeIdxList`, in exactly
  `nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 15) + 4` steps;
* `mergeIdxList_blocksIdx` (round trip): merging the routed lists, back in forward order, with
  the same code restores the stream; `mergeIdx_exec_blocks` is its machine form;
* `mergeIdxList_perm`, `mergeIdxList_perm_blk`: merging with an output code matched to the
  input code by an order-preserving bijection `π` outputs the records permuted by `π`.

In both programs the fields end at index `i₀ + nb`, and every register other than the moved
stream registers and the fields ends as it started. `routeIdx_steps_le` and `mergeIdx_steps_le`
restate the step counts as `nb * (4 * B + 6 * (L * (nr + 1) + ∑ f, len f + nf) + c') + c''`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2


variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {nf nr nd : ℕ}

/-! ### Block lists by index code -/

section Lists

variable {α : Type}

/-- Block `n` of `l`: symbols `n * B, …, n * B + B - 1`. -/
def blk (l : List α) (B n : ℕ) : List α := (l.drop (n * B)).take B

/-- The blocks `n < nb` of `l` whose index `i₀ + n` has code `d`, concatenated in increasing
order. -/
def blocksIdx (l : List α) (B nb : ℕ) (code : ℕ → Fin nd) (i₀ : ℕ) (d : Fin nd) : List α :=
  ((List.range nb).filter fun n => code (i₀ + n) = d).flatMap (blk l B)

/-- The number of indices `j + n`, `n < m`, with code `d`. -/
def idxCount (code : ℕ → Fin nd) (j m : ℕ) (d : Fin nd) : ℕ :=
  ((List.range m).filter fun n => code (j + n) = d).length

lemma blocksIdx_eq_blocksAt (l : List α) (B nb : ℕ) (code : ℕ → Fin nd) (i₀ : ℕ) (d : Fin nd) :
    blocksIdx l B nb code i₀ d = blocksAt l B 0 code d i₀ nb := by
  simp [blocksIdx, blocksAt]
  rfl

@[simp] lemma blocksIdx_zero (l : List α) (B : ℕ) (code : ℕ → Fin nd) (i₀ : ℕ) (d : Fin nd) :
    blocksIdx l B 0 code i₀ d = [] := by simp [blocksIdx]

lemma blocksIdx_succ (l : List α) (B m : ℕ) (code : ℕ → Fin nd) (i₀ : ℕ) (d : Fin nd) :
    blocksIdx l B (m + 1) code i₀ d =
      (if code i₀ = d then l.take B else []) ++ blocksIdx (l.drop B) B m code (i₀ + 1) d := by
  rw [blocksIdx_eq_blocksAt, blocksIdx_eq_blocksAt, blocksAt_succ, Nat.mod_zero]

lemma idxCount_succ (code : ℕ → Fin nd) (j m : ℕ) (d : Fin nd) :
    idxCount code j (m + 1) d = (if code j = d then 1 else 0) + idxCount code (j + 1) m d := by
  have hp : ((fun n => decide (code (j + n) = d)) ∘ Nat.succ) =
      fun n => decide (code (j + 1 + n) = d) := by
    funext n
    simp only [Function.comp_apply, Nat.succ_eq_add_one, show j + (n + 1) = j + 1 + n by omega]
  rw [idxCount, idxCount, List.range_succ_eq_map, List.filter_cons, List.filter_map, hp]
  by_cases h : code j = d <;> simp [h, Nat.add_comm]

lemma length_blk {l : List α} {B nb n : ℕ} (hl : l.length = nb * B) (hn : n < nb) :
    (blk l B n).length = B := by
  have : B ≤ l.length - n * B := by
    rw [hl, ← Nat.sub_mul]
    exact Nat.le_mul_of_pos_left B (by omega)
  simp [blk, this]

lemma length_blocksIdx (code : ℕ → Fin nd) (B : ℕ) :
    ∀ (nb i₀ : ℕ) (l : List α) (d : Fin nd), l.length = nb * B →
      (blocksIdx l B nb code i₀ d).length = idxCount code i₀ nb d * B := by
  intro nb
  induction nb with
  | zero => intro _ _ _ _; simp [idxCount]
  | succ nb ih =>
      intro i₀ l d hl
      have hB : B ≤ l.length := by rw [hl]; nlinarith
      rw [blocksIdx_succ, idxCount_succ, List.length_append,
        ih _ _ _ (by simp [hl, Nat.add_one_mul])]
      by_cases h : code i₀ = d
      · simp [h, hB]; ring
      · simp [h]

/-- Merging blocks by index code, as lists: for the output indices `j, j + 1, …, j + m - 1`,
take one block of `B` symbols from the front of source `s (code j)`. Returns the merged list and
the remaining sources. -/
def mergeIdxList (B : ℕ) (code : ℕ → Fin nd) :
    ℕ → ℕ → (Fin nd → List α) → List α × (Fin nd → List α)
  | 0, _, s => ([], s)
  | m + 1, j, s =>
      let r := mergeIdxList B code m (j + 1) (Function.update s (code j) ((s (code j)).drop B))
      ((s (code j)).take B ++ r.1, r.2)

/-- Round trip: merging the routed block lists `blocksIdx l B nb code i₀ d` (in forward order,
each on top of a remainder `rest d`) with the same code restores `l` and leaves the
remainders. -/
theorem mergeIdxList_blocksIdx (B : ℕ) (code : ℕ → Fin nd) :
    ∀ (nb i₀ : ℕ) (l : List α) (rest : Fin nd → List α), l.length = nb * B →
      mergeIdxList B code nb i₀ (fun d => blocksIdx l B nb code i₀ d ++ rest d) = (l, rest) := by
  intro nb
  induction nb with
  | zero =>
      intro i₀ l rest hl
      obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      simp [mergeIdxList]
  | succ nb ih =>
      intro i₀ l rest hl
      have hB : (l.take B).length = B := by
        simp only [List.length_take]; rw [hl]; apply Nat.min_eq_left; nlinarith
      have hsrc : blocksIdx l B (nb + 1) code i₀ (code i₀) ++ rest (code i₀) =
          l.take B ++ (blocksIdx (l.drop B) B nb code (i₀ + 1) (code i₀) ++ rest (code i₀)) := by
        rw [blocksIdx_succ]; simp
      have hupd : Function.update (fun d => blocksIdx l B (nb + 1) code i₀ d ++ rest d) (code i₀)
          ((blocksIdx l B (nb + 1) code i₀ (code i₀) ++ rest (code i₀)).drop B) =
          fun d => blocksIdx (l.drop B) B nb code (i₀ + 1) d ++ rest d := by
        funext d
        by_cases hd : d = code i₀
        · subst hd
          rw [Function.update_self, hsrc, List.drop_left' hB]
        · rw [Function.update_of_ne hd, blocksIdx_succ]
          simp [Ne.symm hd]
      simp only [mergeIdxList]
      rw [hupd, ih _ _ _ (by simp [hl, Nat.add_one_mul]), hsrc, List.take_left' hB,
        List.take_append_drop]

/-- A list `ns` sorted increasingly, filtered by `p`, starts with its least element `s`
satisfying `p`, followed by the elements satisfying `q`, when `p` is `q` or equal to `s`. -/
lemma filter_eq_cons_of_min {p q : ℕ → Bool} {s : ℕ} :
    ∀ (ns : List ℕ), ns.Pairwise (· < ·) → s ∈ ns → (∀ n ∈ ns, p n = (q n || n == s)) →
      (∀ n ∈ ns, p n = true → s ≤ n) → q s = false → ns.filter p = s :: ns.filter q := by
  intro ns
  induction ns with
  | nil => intro _ hs; simp at hs
  | cons x xs ih =>
      intro hsort hs hpq hmin hqs
      rw [List.pairwise_cons] at hsort
      by_cases hx : x = s
      · subst hx
        have hpx : p x = true := by simp [hpq x List.mem_cons_self]
        rw [List.filter_cons_of_pos hpx, List.filter_cons_of_neg (by simp [hqs])]
        congr 1
        apply List.filter_congr
        intro y hy
        have hxy := hsort.1 y hy
        rw [hpq y (List.mem_cons_of_mem _ hy)]
        simp [Nat.ne_of_gt hxy]
      · have hs' : s ∈ xs := by
          rcases List.mem_cons.1 hs with h | h
          · exact absurd h.symm hx
          · exact h
        have hpx : p x = false := by
          by_contra hpx
          have h1 := hmin x List.mem_cons_self (by simpa using hpx)
          have h2 := hsort.1 s hs'
          omega
        have hqx : q x = false := by
          have h' := (hpq x List.mem_cons_self).symm
          rw [hpx, Bool.or_eq_false_iff] at h'
          exact h'.1
        rw [List.filter_cons_of_neg (by simp [hpx]), List.filter_cons_of_neg (by simp [hqx])]
        exact ih hsort.2 hs' (fun n hn => hpq n (List.mem_cons_of_mem _ hn))
          (fun n hn => hmin n (List.mem_cons_of_mem _ hn)) hqs

/-- Permutation form of merging. Input record `n < nb` (index `i₀ + n`) is routed to source
`cin (i₀ + n)`; output index `j₀ + j` takes a block from source `cout (j₀ + j)`. If `π` is a
bijection of `[0, nb)` with inverse `σ` sending each record to an output position with the same
code (`hcode`) and preserving the order of records with the same code (`hmono`), then merging
the routed sources outputs the records permuted by `π`: output block `j` is input block
`σ j`. -/
theorem mergeIdxList_perm (B nb : ℕ) (l : List α) (hl : l.length = nb * B)
    (cin cout : ℕ → Fin nd) (i₀ j₀ : ℕ) (π σ : ℕ → ℕ) (hπ : ∀ n < nb, π n < nb)
    (hσ : ∀ j < nb, σ j < nb) (hσπ : ∀ n < nb, σ (π n) = n) (hπσ : ∀ j < nb, π (σ j) = j)
    (hcode : ∀ n < nb, cout (j₀ + π n) = cin (i₀ + n))
    (hmono : ∀ n < nb, ∀ n' < nb, cin (i₀ + n) = cin (i₀ + n') → n < n' → π n < π n')
    (rest : Fin nd → List α) :
    mergeIdxList B cout nb j₀ (fun d => blocksIdx l B nb cin i₀ d ++ rest d) =
      ((List.range nb).flatMap (fun j => blk l B (σ j)), rest) := by
  -- the sources after `k` outputs
  let src : ℕ → Fin nd → List α := fun k d =>
    ((List.range nb).filter fun n => decide (cin (i₀ + n) = d ∧ k ≤ π n)).flatMap (blk l B) ++
      rest d
  have key : ∀ m k, k + m = nb →
      mergeIdxList B cout m (j₀ + k) (src k) =
        ((List.range m).flatMap (fun j => blk l B (σ (k + j))), rest) := by
    intro m
    induction m with
    | zero =>
        intro k hk
        simp only [Nat.add_zero] at hk
        subst hk
        have : src k = rest := by
          funext d
          simp only [src]
          rw [List.filter_eq_nil_iff.2 (fun n hn => by
            have := hπ n (List.mem_range.1 hn)
            simp only [decide_eq_true_eq, not_and, not_le]
            intro _; exact this)]
          simp
        simp [mergeIdxList, this]
    | succ m ih =>
        intro k hk
        have hk' : k < nb := by omega
        set d := cout (j₀ + k) with hd
        set s := σ k with hs
        have hsn : s < nb := hσ k hk'
        have hπs : π s = k := hπσ k hk'
        have hcs : cin (i₀ + s) = d := by rw [← hcode s hsn, hπs]
        have hfil : (List.range nb).filter (fun n => decide (cin (i₀ + n) = d ∧ k ≤ π n)) =
            s :: (List.range nb).filter (fun n => decide (cin (i₀ + n) = d ∧ k + 1 ≤ π n)) := by
          apply filter_eq_cons_of_min _ List.pairwise_lt_range (List.mem_range.2 hsn)
          · intro n hn
            have hn' := List.mem_range.1 hn
            by_cases hns : n = s
            · subst hns; simp [hcs, hπs]
            · have : π n ≠ k := fun h => hns (by rw [← hσπ n hn', h])
              have hb : (n == s) = false := by simpa using hns
              rw [hb, Bool.or_false]
              by_cases hc : cin (i₀ + n) = d
              · simp only [hc, true_and, decide_eq_decide]
                constructor <;> intro <;> omega
              · simp [hc]
          · intro n hn hp
            have hn' := List.mem_range.1 hn
            simp only [decide_eq_true_eq] at hp
            by_contra hlt
            have := hmono n hn' s hsn (by rw [hp.1, hcs]) (by omega)
            omega
          · simp [hπs]
        have hsrc_d : src k d = blk l B s ++ src (k + 1) d := by
          simp only [src]; rw [hfil]; simp
        have hupd : Function.update (src k) d ((src k d).drop B) = src (k + 1) := by
          funext d'
          by_cases hd' : d' = d
          · subst hd'
            rw [Function.update_self, hsrc_d, List.drop_left' (length_blk hl hsn)]
          · rw [Function.update_of_ne hd']
            simp only [src]
            congr 2
            apply List.filter_congr
            intro n hn
            have hn' := List.mem_range.1 hn
            by_cases hns : n = s
            · subst hns; simp [hcs, Ne.symm hd']
            · have : π n ≠ k := fun h => hns (by rw [← hσπ n hn', h])
              simp only [decide_eq_decide]
              constructor
              · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
              · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        simp only [mergeIdxList]
        rw [← hd, hupd, show j₀ + k + 1 = j₀ + (k + 1) by ring, ih (k + 1) (by omega), hsrc_d,
          List.take_left' (length_blk hl hsn)]
        simp only [Prod.mk.injEq, and_true]
        rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_zero]
        congr 1
        congr 1
        funext j
        simp only [Nat.succ_eq_add_one]
        rw [show k + (j + 1) = k + 1 + j by ring]
  have h0 : src 0 = fun d => blocksIdx l B nb cin i₀ d ++ rest d := by
    funext d
    simp [src, blocksIdx]
  rw [← h0, show j₀ = j₀ + 0 from rfl, key nb 0 (by simp)]
  simp

lemma length_flatMap_range {g : ℕ → List α} {B : ℕ} :
    ∀ nb, (∀ j < nb, (g j).length = B) → ((List.range nb).flatMap g).length = nb * B := by
  intro nb
  induction nb with
  | zero => intro _; simp
  | succ nb ih =>
      intro hg
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append,
        ih (fun j hj => hg j (by omega)), hg nb (by omega), Nat.add_one_mul]

/-- Block `j` of a concatenation of `nb` blocks of length `B` is the `j`-th block. -/
lemma blk_flatMap_range {g : ℕ → List α} {B : ℕ} :
    ∀ nb, (∀ j < nb, (g j).length = B) → ∀ j < nb, blk ((List.range nb).flatMap g) B j = g j := by
  intro nb
  induction nb with
  | zero => intro _ j hj; omega
  | succ nb ih =>
      intro hg j hj
      have hlen := length_flatMap_range nb (fun j hj => hg j (by omega))
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      by_cases hjn : j < nb
      · have h1 : j * B ≤ ((List.range nb).flatMap g).length := by rw [hlen]; nlinarith
        have h2 : B ≤ (((List.range nb).flatMap g).drop (j * B)).length := by
          rw [List.length_drop, hlen, ← Nat.sub_mul]
          exact Nat.le_mul_of_pos_left B (by omega)
        rw [blk, List.drop_append_of_le_length h1, List.take_append_of_le_length h2]
        exact ih (fun j hj => hg j (by omega)) j hjn
      · obtain rfl : j = nb := by omega
        rw [blk, List.drop_left' hlen, List.take_of_length_le (by rw [hg j hj])]

/-- `mergeIdxList_perm` block by block: output block `π n` is input block `n`. -/
theorem mergeIdxList_perm_blk (B nb : ℕ) (l : List α) (hl : l.length = nb * B)
    (cin cout : ℕ → Fin nd) (i₀ j₀ : ℕ) (π σ : ℕ → ℕ) (hπ : ∀ n < nb, π n < nb)
    (hσ : ∀ j < nb, σ j < nb) (hσπ : ∀ n < nb, σ (π n) = n) (hπσ : ∀ j < nb, π (σ j) = j)
    (hcode : ∀ n < nb, cout (j₀ + π n) = cin (i₀ + n))
    (hmono : ∀ n < nb, ∀ n' < nb, cin (i₀ + n) = cin (i₀ + n') → n < n' → π n < π n')
    (rest : Fin nd → List α) :
    (mergeIdxList B cout nb j₀ (fun d => blocksIdx l B nb cin i₀ d ++ rest d)).1.length =
        nb * B ∧
      ∀ n < nb,
        blk (mergeIdxList B cout nb j₀ (fun d => blocksIdx l B nb cin i₀ d ++ rest d)).1 B (π n) =
          blk l B n := by
  rw [mergeIdxList_perm B nb l hl cin cout i₀ j₀ π σ hπ hσ hσπ hπσ hcode hmono rest]
  have hg : ∀ j < nb, (blk l B (σ j)).length = B := fun j hj => length_blk hl (hσ j hj)
  refine ⟨length_flatMap_range nb hg, fun n hn => ?_⟩
  rw [blk_flatMap_range nb hg (π n) (hπ n hn), hσπ n hn]

end Lists

/-! ### Record codes and the index layout -/

/-- Value of code-pass register `r` at index `i`: digit `f` of `i` if `rsrc r = .inl f` (a
counter field), the constant `p` if `rsrc r = .inr p` (a parameter register). -/
def regVal (len : Fin nf → ℕ) (rsrc : Fin nr → Fin nf ⊕ ℕ) (i : ℕ) (r : Fin nr) : ℕ :=
  Sum.elim (fun f => digit len f i) id (rsrc r)

/-- The code of record index `i`: the output of `C` on the low `L` bits of the code-pass
registers at index `i`. -/
def idxCode (C : CAuto A nr nd) (L : ℕ) (len : Fin nf → ℕ) (rsrc : Fin nr → Fin nf ⊕ ℕ)
    (i : ℕ) : Fin nd :=
  C.eval L (regVal len rsrc i)

/-- The destination selector of a state symbol, for `xferBlock`. -/
def codeSel (C : CAuto A nr nd) (n : ℕ) : Fin nd := C.out ⟨n % (A + 4), Nat.mod_lt _ (by omega)⟩

@[simp] lemma codeSel_val (C : CAuto A nr nd) (x : Fin (A + 4)) : codeSel C x.val = C.out x := by
  simp [codeSel, Nat.mod_eq_of_lt x.isLt]

/-- Register layout of the index machinery beside a set `X` of other registers in use: field
registers `cf`; code-pass registers `rs`, each either a field of length `L` (`rsrc r = .inl f`)
or a parameter register outside the fields (`rsrc r = .inr p`); spare registers `tmps`; and the
code slot `st`. -/
structure IdxLayout (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ ℕ) (st : Fin T) (X : Fin T → Prop) : Prop
    extends CodeLayout rs tmps st where
  cf_inj : Function.Injective cf
  tmps_cf : ∀ r f, tmps r ≠ cf f
  field : ∀ r f, rsrc r = .inl f → rs r = cf f ∧ len f = L
  param : ∀ r p f, rsrc r = .inr p → rs r ≠ cf f
  cf_X : ∀ f, ¬ X (cf f)
  rs_X : ∀ r, ¬ X (rs r)
  tmps_X : ∀ r, ¬ X (tmps r)

/-- Registers at index `i`: the fields hold the digits of `i`, the parameter registers their
constants, and the spare registers `tmps` are empty. -/
def IdxState (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ ℕ) (R : Fin T → List (Fin (A + 4))) (i : ℕ) : Prop :=
  (∀ f, R (cf f) = binSyms (len f) (digit len f i)) ∧
    (∀ r p, rsrc r = .inr p → R (rs r) = binSyms L p) ∧ ∀ r, R (tmps r) = []

section Layout

variable {cf : Fin nf → Fin T} {len : Fin nf → ℕ} {L : ℕ} {rs tmps : Fin nr → Fin T}
  {rsrc : Fin nr → Fin nf ⊕ ℕ} {st : Fin T} {X : Fin T → Prop}

lemma IdxState.rs_eq (h : IdxLayout cf len L rs tmps rsrc st X) {R : Fin T → List (Fin (A + 4))}
    {i : ℕ} (hI : IdxState cf len L rs tmps rsrc R i) (r : Fin nr) :
    R (rs r) = binSyms L (regVal len rsrc i r) := by
  rcases hr : rsrc r with f | p
  · obtain ⟨h1, h2⟩ := h.field r f hr
    rw [h1, hI.1 f, h2]
    simp [regVal, hr]
  · rw [hI.2.1 r p hr]
    simp [regVal, hr]

/-- The index state survives changes outside the index registers. -/
lemma IdxState.of_frame (h : IdxLayout cf len L rs tmps rsrc st X)
    {R R' : Fin T → List (Fin (A + 4))} {i : ℕ} (hI : IdxState cf len L rs tmps rsrc R i)
    (hR : ∀ k, ¬ X k → R' k = R k) : IdxState cf len L rs tmps rsrc R' i :=
  ⟨fun f => by rw [hR _ (h.cf_X f), hI.1 f],
    fun r p hr => by rw [hR _ (h.rs_X r), hI.2.1 r p hr],
    fun r => by rw [hR _ (h.tmps_X r), hI.2.2 r]⟩

/-- The index state after an increment of the fields. -/
lemma IdxState.of_incr (h : IdxLayout cf len L rs tmps rsrc st X)
    {R R' : Fin T → List (Fin (A + 4))} {i : ℕ} (hI : IdxState cf len L rs tmps rsrc R i)
    (hcf : ∀ f, R' (cf f) = binSyms (len f) (digit len f (i + 1)))
    (hR : ∀ k, (∀ f, k ≠ cf f) → R' k = R k) : IdxState cf len L rs tmps rsrc R' (i + 1) :=
  ⟨hcf, fun r p hr => by rw [hR _ (h.param r p · hr), hI.2.1 r p hr],
    fun r => by rw [hR _ (h.tmps_cf r), hI.2.2 r]⟩

end Layout

/-- One record of the index loops: a code pass on the current index into slot `st`, one block
of `|ctr|` symbols from `src (code)` to `dst (code)` by `xferBlock`, an increment of the fields
`cf` (carry in slot `st`), then the action `fin`. -/
def idxStep [NeZero nr] (src dst : Fin nd → Fin T) (ctr tmp : Fin T) (cf : Fin nf → Fin T)
    (rs tmps : Fin nr → Fin T) (st : Fin T) (C : CAuto A nr nd) (fin : Act T Q A U) :
    Pr P T Q A U :=
  .seq (codePass rs tmps st C)
    (.seq (xferBlock src dst ctr tmp st 1 (codeSel C) .done)
      (.seq (incrFields cf tmp st) (.act fin)))

/-- One record: the code `d` of index `i` selects the transfer of `ys` (as many symbols as
`ctr`) from the top of `src d` to `dst d`; then the fields advance to `i + 1`. Exactly
`4 * |ctr| + 6 * L + 4 * (∑ f, len f) + 4 * nf + 12` steps, the final action `fin` included. -/
theorem idxStep_exec [NeZero nr] (src dst : Fin nd → Fin T) (ctr tmp : Fin T)
    (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ ℕ) (st : Fin T) (C : CAuto A nr nd) (fin : Act T Q A U) (i : ℕ)
    {X : Fin T → Prop} (h : IdxLayout cf len L rs tmps rsrc st X)
    (hX : ∀ k, k = ctr ∨ k = tmp ∨ k = src (idxCode C L len rsrc i) ∨
      k = dst (idxCode C L len rsrc i) → X k)
    (h1 : src (idxCode C L len rsrc i) ≠ ctr) (h2 : src (idxCode C L len rsrc i) ≠ tmp)
    (h3 : ctr ≠ tmp) (h4 : dst (idxCode C L len rsrc i) ≠ src (idxCode C L len rsrc i))
    (h5 : dst (idxCode C L len rsrc i) ≠ ctr) (h6 : dst (idxCode C L len rsrc i) ≠ tmp)
    (c ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hlen : c.length = ys.length) (hc : S.R ctr = c) (ht : S.R tmp = [])
    (hs : S.R (src (idxCode C L len rsrc i)) = ys ++ rest)
    (hI : IdxState cf len L rs tmps rsrc S.R i) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      Exec body (idxStep src dst ctr tmp cf rs tmps st C fin) (mk v S)
        (4 * c.length + 6 * L + 4 * (∑ f, len f) + 4 * nf + 12) (fin.run (mk v' { S with R := R' })) ∧
      R' (src (idxCode C L len rsrc i)) = rest ∧
      R' (dst (idxCode C L len rsrc i)) = ys.reverse ++ S.R (dst (idxCode C L len rsrc i)) ∧
      IdxState cf len L rs tmps rsrc R' (i + 1) ∧
      ∀ k, k ≠ src (idxCode C L len rsrc i) → k ≠ dst (idxCode C L len rsrc i) →
        (∀ f, k ≠ cf f) → R' k = S.R k := by
  set d := idxCode C L len rsrc i with hd
  obtain ⟨v₁, hu₁, hs₁, he₁⟩ := codePass_exec body h.toCodeLayout C L (regVal len rsrc i) v S
    (hI.rs_eq h) hI.2.2
  obtain ⟨v₂, R₁, hu₂, _, he₂, hctr₁, htmp₁, hsrc₁, hdst₁, hoth₁⟩ :=
    xferBlock_exec body src dst ctr tmp st 1 (codeSel C) .done d h1 h2 h3 h4 h5 h6 c ys rest v₁ S
      hlen hc ht hs (by rw [hs₁, codeSel_val]; rfl)
  rw [run_done] at he₂
  have hfr₁ : ∀ k, ¬ X k → R₁ k = S.R k := fun k hk =>
    hoth₁ k (fun e => hk (hX k (Or.inr (Or.inr (Or.inl e)))))
      (fun e => hk (hX k (Or.inl e))) (fun e => hk (hX k (Or.inr (Or.inl e))))
      (fun e => hk (hX k (Or.inr (Or.inr (Or.inr e)))))
  have hI₁ : IdxState cf len L rs tmps rsrc R₁ i := hI.of_frame h hfr₁
  obtain ⟨v₃, R₂, hu₃, he₃, hcf₃, hoth₃⟩ := incrFields_exec body cf h.cf_inj tmp st
    (fun f e => h.cf_X f (hX _ (Or.inr (Or.inl e)))) len i _ { S with R := R₁ } htmp₁ hI₁.1
  refine ⟨v₃, R₂, by rw [hu₃]; simp [hu₂, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂
    (Exec.seq he₃ (Exec.act (body := body) fin _)))) (by ring) rfl, ?_, ?_,
    hI₁.of_incr h hcf₃ hoth₃, ?_⟩
  · rw [hoth₃ _ (fun f e => h.cf_X f (hX _ (Or.inr (Or.inr (Or.inl e.symm)))))]
    exact hsrc₁
  · rw [hoth₃ _ (fun f e => h.cf_X f (hX _ (Or.inr (Or.inr (Or.inr e.symm)))))]
    exact hdst₁
  · intro k hk1 hk2 hk3
    rw [hoth₃ k hk3]
    show R₁ k = S.R k
    by_cases hkc : k = ctr
    · subst hkc; rw [hctr₁, hc]
    by_cases hkt : k = tmp
    · subst hkt; rw [htmp₁, ht]
    exact hoth₁ k hk1 hkc hkt hk2

/-! ### Routing -/

/-- The stream registers of `routeIdx`. -/
def routeRegs (src : Fin T) (dst : Fin nd → Fin T) (ctr tmp : Fin T) (k : Fin T) : Prop :=
  k = src ∨ k = ctr ∨ k = tmp ∨ ∃ d, dst d = k

/-- Route the records of `src` by index code: while `src` is nonempty, compute the code `d` of
the current index, move one block of `|ctr|` symbols from `src` onto `dst d`, and increment the
index. -/
def routeIdx [NeZero nr] (src : Fin T) (dst : Fin nd → Fin T) (ctr tmp : Fin T)
    (cf : Fin nf → Fin T) (rs tmps : Fin nr → Fin T) (st : Fin T) (C : CAuto A nr nd) :
    Pr P T Q A U :=
  .seq (.act (peekR src))
    (.loop (·.flag) (idxStep (fun _ => src) dst ctr tmp cf rs tmps st C (peekR src)))

/-- The record loop of `routeIdx`, from index `i` with `m` records left. -/
theorem routeIdx_loop [NeZero nr] (src : Fin T) (dst : Fin nd → Fin T) (ctr tmp : Fin T)
    (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ ℕ) (st : Fin T) (C : CAuto A nr nd)
    (h : IdxLayout cf len L rs tmps rsrc st (routeRegs src dst ctr tmp))
    (h1 : src ≠ ctr) (h2 : src ≠ tmp) (h3 : ctr ≠ tmp) (h4 : ∀ d, dst d ≠ src)
    (h5 : ∀ d, dst d ≠ ctr) (h6 : ∀ d, dst d ≠ tmp) (hinj : Function.Injective dst) {B : ℕ}
    (hB : 1 ≤ B) (c : List (Fin (A + 4))) (hcB : c.length = B) :
    ∀ (m i : ℕ) (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      l.length = m * B → S.R src = l → S.R ctr = c → S.R tmp = [] →
      IdxState cf len L rs tmps rsrc S.R i → v.flag = l.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (.loop (·.flag) (idxStep (fun _ => src) dst ctr tmp cf rs tmps st C (peekR src)))
          (mk v S) (m * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 13) + 1)
          (mk v' { S with R := R' }) ∧
        R' src = [] ∧ IdxState cf len L rs tmps rsrc R' (i + m) ∧
        (∀ d, R' (dst d) = (blocksIdx l B m (idxCode C L len rsrc) i d).reverse ++ S.R (dst d)) ∧
        ∀ k, k ≠ src → (∀ d, dst d ≠ k) → (∀ f, cf f ≠ k) → R' k = S.R k := by
  intro m
  induction m with
  | zero =>
      intro i l v S hl hs _ _ hI hf
      obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      exact ⟨v, S.R, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) rfl, hs, hI,
        fun d => by simp, fun _ _ _ _ => rfl⟩
  | succ m ih =>
      intro i l v S hl hs hc ht hI hf
      have hlB : B ≤ l.length := by rw [hl]; nlinarith
      obtain ⟨v₁, R₁, hu₁, he₁, hsrc₁, hdst₁, hI₁, hoth₁⟩ :=
        idxStep_exec body (fun _ => src) dst ctr tmp cf len L rs tmps rsrc st C (peekR src) i h
          (fun k hk => by rcases hk with rfl | rfl | rfl | rfl <;> simp [routeRegs])
          h1 h2 h3 (h4 _) (h5 _) (h6 _) c (l.take B) (l.drop B) v S (by simp [hcB]; omega) hc ht
          (by simp [hs]) hI
      rw [peekR_run] at he₁
      have hfr₁ : ∀ k, k ≠ src → k ≠ dst (idxCode C L len rsrc i) → (∀ f, cf f ≠ k) →
          R₁ k = S.R k :=
        fun k hk1 hk2 hk3 => hoth₁ k hk1 hk2 (fun f => (hk3 f).symm)
      have hcf : ∀ f k, routeRegs src dst ctr tmp k → cf f ≠ k :=
        fun f k hk e => h.cf_X f (e ▸ hk)
      have hctr₁ : R₁ ctr = c := by
        rw [← hc]
        exact hfr₁ ctr (Ne.symm h1) (Ne.symm (h5 _)) (fun f => hcf f _ (by simp [routeRegs]))
      have htmp₁ : R₁ tmp = [] := by
        rw [← ht]
        exact hfr₁ tmp (Ne.symm h2) (Ne.symm (h6 _)) (fun f => hcf f _ (by simp [routeRegs]))
      obtain ⟨v', R', hu, he, hsrc, hI', hdst, hoth⟩ := ih (i + 1) (l.drop B)
        { v₁ with flag := (R₁ src).head?.isSome } { S with R := R₁ }
        (by simp [hl, Nat.add_one_mul]) hsrc₁ hctr₁ htmp₁ hI₁ (by simp [hsrc₁])
      have hne : l ≠ [] := by
        intro e; rw [e] at hlB; simp at hlB; omega
      refine ⟨v', R', by rw [hu, hu₁], Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
        (by simpa [hf] using hne) he₁ he) (by rw [hcB]; ring) rfl, hsrc,
        by rw [show i + (m + 1) = i + 1 + m by ring]; exact hI', ?_, ?_⟩
      · intro d
        rw [hdst, blocksIdx_succ]
        show (blocksIdx _ B m _ (i + 1) d).reverse ++ R₁ (dst d) = _
        by_cases hd : idxCode C L len rsrc i = d
        · subst hd
          simp [hdst₁]
        · rw [hfr₁ (dst d) (h4 d) (fun e => hd (hinj e).symm)
            (fun f => hcf f _ (by simp [routeRegs]))]
          simp [hd]
      · intro k hk1 hk2 hk3
        exact (hoth k hk1 hk2 hk3).trans (hfr₁ k hk1 (fun e => hk2 _ e.symm) hk3)

/-- Routing `nb` records of `B ≥ 1` symbols by index code. The stream `l` is in `src`, the
counter `ctr` holds `B` symbols, `tmp` is empty, and the index registers hold index `i₀`.
Afterwards `src` is empty, `dst d` gains the reversal of the records whose index has code `d`
(`blocksIdx`), the fields hold index `i₀ + nb`, and every other register, `ctr`, `tmp`, the
parameter registers and `tmps` included, is unchanged. Exactly
`nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 13) + 2` steps. -/
theorem routeIdx_exec [NeZero nr] (src : Fin T) (dst : Fin nd → Fin T) (ctr tmp : Fin T)
    (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ ℕ) (st : Fin T) (C : CAuto A nr nd)
    (h : IdxLayout cf len L rs tmps rsrc st (routeRegs src dst ctr tmp))
    (hreg : [src, ctr, tmp].Nodup) (hdst : ∀ d, dst d ∉ [src, ctr, tmp])
    (hinj : Function.Injective dst) {l c : List (Fin (A + 4))} {nb B i₀ : ℕ} (hB : 1 ≤ B)
    (hl : l.length = nb * B) (hcB : c.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = l) (hc : S.R ctr = c) (ht : S.R tmp = [])
    (hI : IdxState cf len L rs tmps rsrc S.R i₀) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      Exec body (routeIdx src dst ctr tmp cf rs tmps st C) (mk v S)
        (nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 13) + 2) (mk v' { S with R := R' }) ∧
      R' src = [] ∧
      (∀ d, R' (dst d) = (blocksIdx l B nb (idxCode C L len rsrc) i₀ d).reverse ++ S.R (dst d)) ∧
      (∀ f, R' (cf f) = binSyms (len f) (digit len f (i₀ + nb))) ∧
      ∀ k, k ≠ src → (∀ d, dst d ≠ k) → (∀ f, cf f ≠ k) → R' k = S.R k := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg hdst
  obtain ⟨⟨h1, h2⟩, h3⟩ := hreg
  obtain ⟨v', R', hu, he, hsrc, hI', hd, hoth⟩ :=
    routeIdx_loop body src dst ctr tmp cf len L rs tmps rsrc st C h h1 h2 h3 (fun d => (hdst d).1)
      (fun d => (hdst d).2.1) (fun d => (hdst d).2.2) hinj hB c hcB nb i₀ l
      { v with flag := (S.R src).head?.isSome } S hl hs hc ht hI (by rw [hs])
  exact ⟨v', R', hu, Exec.cast (Exec.seq (peekR_run src v S ▸
    Exec.act (body := body) (peekR src) (mk v S)) he) (by ring) rfl, hsrc, hd, hI'.1, hoth⟩

/-- The step count of `routeIdx_exec` in the form
`nb * (4 * B + c * (L * (nr + 1) + ∑ f, len f + nf) + c') + c''`, with `c = 6`, `c' = 13`,
`c'' = 2`. -/
lemma routeIdx_steps_le (nb B L : ℕ) (len : Fin nf → ℕ) :
    nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 13) + 2 ≤
      nb * (4 * B + 6 * (L * (nr + 1) + ∑ f, len f + nf) + 13) + 2 := by
  have : L ≤ L * (nr + 1) := Nat.le_mul_of_pos_right L (by omega)
  have : 4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 13 ≤
      4 * B + 6 * (L * (nr + 1) + ∑ f, len f + nf) + 13 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left nb this) 2

/-! ### Merging -/

/-- The stream registers of `mergeIdx`. -/
def mergeRegs (srcs : Fin nd → Fin T) (dst ctr tmp cnt ctmp : Fin T) (k : Fin T) : Prop :=
  k = dst ∨ k = ctr ∨ k = tmp ∨ k = cnt ∨ k = ctmp ∨ ∃ d, srcs d = k

/-- Merge records by index code: for each symbol of `cnt`, compute the code `d` of the current
index, move one block of `|ctr|` symbols from `srcs d` onto `dst`, and increment the index.
Each record moves one symbol of `cnt` onto `ctmp`; a final `moveR` moves `ctmp` back. -/
def mergeIdx [NeZero nr] (srcs : Fin nd → Fin T) (dst ctr tmp cnt ctmp : Fin T)
    (cf : Fin nf → Fin T) (rs tmps : Fin nr → Fin T) (st : Fin T) (C : CAuto A nr nd) :
    Pr P T Q A U :=
  .seq (.act (peekR cnt))
    (.seq (.loop (·.flag)
        (idxStep srcs (fun _ => dst) ctr tmp cf rs tmps st C (moveStep cnt ctmp id)))
      (moveR ctmp cnt id))

/-- The record loop of `mergeIdx`, from index `j` with the records left counted by `kk` and the
sources holding `s`. -/
theorem mergeIdx_loop [NeZero nr] (srcs : Fin nd → Fin T) (dst ctr tmp cnt ctmp : Fin T)
    (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ ℕ) (st : Fin T) (C : CAuto A nr nd)
    (h : IdxLayout cf len L rs tmps rsrc st (mergeRegs srcs dst ctr tmp cnt ctmp))
    (h1 : ∀ d, srcs d ≠ ctr) (h2 : ∀ d, srcs d ≠ tmp) (h3 : ctr ≠ tmp) (h4 : ∀ d, dst ≠ srcs d)
    (h5 : dst ≠ ctr) (h6 : dst ≠ tmp) (h7 : ∀ d, srcs d ≠ cnt) (h8 : ∀ d, srcs d ≠ ctmp)
    (h9 : dst ≠ cnt) (h10 : dst ≠ ctmp) (h11 : ctr ≠ cnt) (h12 : ctr ≠ ctmp) (h13 : tmp ≠ cnt)
    (h14 : tmp ≠ ctmp) (h15 : cnt ≠ ctmp) (hinj : Function.Injective srcs) {B : ℕ}
    (c : List (Fin (A + 4))) (hcB : c.length = B) :
    ∀ (kk : List (Fin (A + 4))) (j : ℕ) (s : Fin nd → List (Fin (A + 4))) (v : HS T Q A U)
      (S : Stacks T A),
      S.R cnt = kk → (∀ d, S.R (srcs d) = s d) →
      (∀ d, idxCount (idxCode C L len rsrc) j kk.length d * B ≤ (s d).length) →
      S.R ctr = c → S.R tmp = [] → IdxState cf len L rs tmps rsrc S.R j →
      v.flag = kk.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (.loop (·.flag)
            (idxStep srcs (fun _ => dst) ctr tmp cf rs tmps st C (moveStep cnt ctmp id)))
          (mk v S) (kk.length * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 13) + 1)
          (mk v' { S with R := R' }) ∧
        R' cnt = [] ∧ R' ctmp = kk.reverse ++ S.R ctmp ∧
        R' dst = (mergeIdxList B (idxCode C L len rsrc) kk.length j s).1.reverse ++ S.R dst ∧
        (∀ d, R' (srcs d) = (mergeIdxList B (idxCode C L len rsrc) kk.length j s).2 d) ∧
        IdxState cf len L rs tmps rsrc R' (j + kk.length) ∧
        ∀ k, k ≠ dst → k ≠ cnt → k ≠ ctmp → (∀ d, srcs d ≠ k) → (∀ f, cf f ≠ k) →
          R' k = S.R k := by
  have hcf : ∀ f k, mergeRegs srcs dst ctr tmp cnt ctmp k → cf f ≠ k :=
    fun f k hk e => h.cf_X f (e ▸ hk)
  intro kk
  induction kk with
  | nil =>
      intro j s v S hk hs _ _ _ hI hf
      exact ⟨v, S.R, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) rfl, hk, rfl,
        by simp [mergeIdxList], fun d => by simp [mergeIdxList, hs], by simpa using hI,
        fun _ _ _ _ _ _ => rfl⟩
  | cons e kk ih =>
      intro j s v S hk hs hfit hc ht hI hf
      set code := idxCode C L len rsrc with hcode
      have hfit₀ := hfit (code j)
      rw [List.length_cons, idxCount_succ] at hfit₀
      simp only [↓reduceIte] at hfit₀
      have hB : B ≤ (s (code j)).length := by nlinarith
      obtain ⟨v₁, R₁, hu₁, he₁, hsrc₁, hdst₁, hI₁, hoth₁⟩ :=
        idxStep_exec body srcs (fun _ => dst) ctr tmp cf len L rs tmps rsrc st C
          (moveStep cnt ctmp id) j h
          (fun k hk => by rcases hk with rfl | rfl | rfl | rfl <;> simp [mergeRegs])
          (h1 _) (h2 _) h3 (h4 _) h5 h6 c ((s (code j)).take B) ((s (code j)).drop B) v S
          (by simp [hcB]; omega) hc ht (by rw [hs, List.take_append_drop]) hI
      have hfr₁ : ∀ k, k ≠ srcs (code j) → k ≠ dst → (∀ f, cf f ≠ k) → R₁ k = S.R k :=
        fun k hk1 hk2 hk3 => hoth₁ k hk1 hk2 (fun f => (hk3 f).symm)
      have hcnt₁ : R₁ cnt = e :: kk := by
        rw [hfr₁ cnt (h7 _).symm h9.symm (fun f => hcf f _ (by simp [mergeRegs])), hk]
      have hct₁ : R₁ ctmp = S.R ctmp :=
        hfr₁ ctmp (h8 _).symm h10.symm (fun f => hcf f _ (by simp [mergeRegs]))
      have hrun : (moveStep cnt ctmp id : Act T Q A U).run (mk v₁ { S with R := R₁ }) =
          mk { v₁ with sym := some e, flag := kk.head?.isSome }
            { S with R := Function.update (Function.update R₁ cnt kk) ctmp (e :: R₁ ctmp) } := by
        simp [moveStep, peekR, Action.run, hcnt₁, update_rt, Function.update_of_ne h15,
          Function.update_of_ne h15.symm]
      rw [hrun] at he₁
      set R₂ := Function.update (Function.update R₁ cnt kk) ctmp (e :: R₁ ctmp) with hR₂
      have hfr₂ : ∀ k, k ≠ cnt → k ≠ ctmp → R₂ k = R₁ k := fun k hk1 hk2 => by
        simp [hR₂, Function.update_of_ne hk1, Function.update_of_ne hk2]
      set s' := Function.update s (code j) ((s (code j)).drop B) with hs'
      obtain ⟨v', R', hu, he, hcnt, hct, hdst, hsrc, hI', hoth⟩ := ih (j + 1) s'
        { v₁ with sym := some e, flag := kk.head?.isSome } { S with R := R₂ }
        (by simp [hR₂, Function.update_of_ne h15])
        (by
          intro d
          show R₂ (srcs d) = s' d
          rw [hfr₂ _ (h7 d) (h8 d)]
          by_cases hd : d = code j
          · subst hd; rw [hsrc₁, hs', Function.update_self]
          · rw [hfr₁ _ (fun e => hd (hinj e)) (h4 d).symm
              (fun f => hcf f _ (by simp [mergeRegs])), hs d, hs', Function.update_of_ne hd])
        (by
          intro d
          have hd' := hfit d
          rw [List.length_cons, idxCount_succ] at hd'
          by_cases hd : d = code j
          · subst hd
            rw [hs', Function.update_self, List.length_drop]
            simp only [↓reduceIte] at hd'
            have := Nat.add_mul 1 (idxCount code (j + 1) kk.length (code j)) B
            omega
          · rw [hs', Function.update_of_ne hd]
            simp only [Ne.symm hd, ↓reduceIte, Nat.zero_add] at hd'
            exact hd')
        (by
          show R₂ ctr = c
          rw [hfr₂ _ h11 h12, hfr₁ _ (h1 _).symm h5.symm
            (fun f => hcf f _ (by simp [mergeRegs])), hc])
        (by
          show R₂ tmp = []
          rw [hfr₂ _ h13 h14, hfr₁ _ (h2 _).symm h6.symm
            (fun f => hcf f _ (by simp [mergeRegs])), ht])
        (hI₁.of_frame h (fun k hk => hfr₂ k (fun e => hk (by simp [mergeRegs, e]))
          (fun e => hk (by simp [mergeRegs, e])))) rfl
      refine ⟨v', R', by rw [hu, hu₁], Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
        (by simpa using hf) he₁ he) (by simp [hcB]; ring) rfl, hcnt, ?_, ?_, hsrc,
        by rw [List.length_cons, show j + (kk.length + 1) = j + 1 + kk.length by ring]; exact hI',
        ?_⟩
      · rw [hct]
        show kk.reverse ++ R₂ ctmp = _
        simp [hR₂, hct₁]
      · rw [hdst]
        show _ ++ R₂ dst = _
        rw [hfr₂ _ h9 h10, hdst₁]
        simp [mergeIdxList, hs']
      · intro k hk1 hk2 hk3 hk4 hk5
        rw [hoth k hk1 hk2 hk3 hk4 hk5]
        show R₂ k = S.R k
        rw [hfr₂ k hk2 hk3]
        exact hfr₁ k (fun e => hk4 _ e.symm) hk1 hk5

/-- Merging `nb` records of `B` symbols by index code (`nb` is the length of `cnt`): the
sources `srcs d` hold `s d`, with enough blocks for every output index (`hfit`); `ctr` holds `B`
symbols; `tmp` and `ctmp` are empty; the index registers hold index `i₀`. Afterwards `dst`
gains the reversal of `(mergeIdxList B code nb i₀ s).1`, the sources hold the remainders
`(mergeIdxList B code nb i₀ s).2`, the fields hold index `i₀ + nb`, and every other register,
`ctr`, `tmp`, `cnt`, `ctmp`, the parameter registers and `tmps` included, is unchanged. Exactly
`nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 15) + 4` steps. -/
theorem mergeIdx_exec [NeZero nr] (srcs : Fin nd → Fin T) (dst ctr tmp cnt ctmp : Fin T)
    (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ ℕ) (st : Fin T) (C : CAuto A nr nd)
    (h : IdxLayout cf len L rs tmps rsrc st (mergeRegs srcs dst ctr tmp cnt ctmp))
    (hreg : [dst, ctr, tmp, cnt, ctmp].Nodup) (hsrcs : ∀ d, srcs d ∉ [dst, ctr, tmp, cnt, ctmp])
    (hinj : Function.Injective srcs) {c kk : List (Fin (A + 4))} {nb B i₀ : ℕ}
    (hcB : c.length = B) (hk : kk.length = nb) (s : Fin nd → List (Fin (A + 4)))
    (hfit : ∀ d, idxCount (idxCode C L len rsrc) i₀ nb d * B ≤ (s d).length)
    (v : HS T Q A U) (S : Stacks T A) (hs : ∀ d, S.R (srcs d) = s d) (hc : S.R ctr = c)
    (ht : S.R tmp = []) (hcnt : S.R cnt = kk) (hct : S.R ctmp = [])
    (hI : IdxState cf len L rs tmps rsrc S.R i₀) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      Exec body (mergeIdx srcs dst ctr tmp cnt ctmp cf rs tmps st C) (mk v S)
        (nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 15) + 4) (mk v' { S with R := R' }) ∧
      R' dst = (mergeIdxList B (idxCode C L len rsrc) nb i₀ s).1.reverse ++ S.R dst ∧
      (∀ d, R' (srcs d) = (mergeIdxList B (idxCode C L len rsrc) nb i₀ s).2 d) ∧
      (∀ f, R' (cf f) = binSyms (len f) (digit len f (i₀ + nb))) ∧
      ∀ k, k ≠ dst → (∀ d, srcs d ≠ k) → (∀ f, cf f ≠ k) → R' k = S.R k := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg hsrcs
  obtain ⟨⟨h5, h6, h9, h10⟩, ⟨h3, h11, h12⟩, ⟨h13, h14⟩, h15⟩ := hreg
  subst hk
  obtain ⟨v₁, R₁, hu₁, he₁, hcnt₁, hct₁, hdst₁, hsrc₁, hI₁, hoth₁⟩ :=
    mergeIdx_loop body srcs dst ctr tmp cnt ctmp cf len L rs tmps rsrc st C h
      (fun d => (hsrcs d).2.1) (fun d => (hsrcs d).2.2.1) h3 (fun d => Ne.symm (hsrcs d).1) h5 h6
      (fun d => (hsrcs d).2.2.2.1) (fun d => (hsrcs d).2.2.2.2) h9 h10 h11 h12 h13 h14 h15 hinj
      c hcB kk i₀ s { v with flag := (S.R cnt).head?.isSome } S hcnt hs hfit hc ht hI
      (by simp [hcnt])
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body ctmp cnt (Ne.symm h15) id v₁ { S with R := R₁ }
  refine ⟨v₂, movedR R₁ ctmp cnt id (R₁ ctmp), by rw [hu₂, hu₁],
    Exec.cast (Exec.seq (peekR_run cnt v S ▸ Exec.act (body := body) (peekR cnt) (mk v S))
      (Exec.seq he₁ he₂)) ?_ rfl, ?_, ?_, ?_, ?_⟩
  · simp [hct₁, hct]; ring
  · simp [movedR, h9, h10, hdst₁]
  · intro d; simp [movedR, (hsrcs d).2.2.2.1, (hsrcs d).2.2.2.2, hsrc₁]
  · intro f
    have hf1 : cf f ≠ cnt := fun e => h.cf_X f (by simp [mergeRegs, e])
    have hf2 : cf f ≠ ctmp := fun e => h.cf_X f (by simp [mergeRegs, e])
    simp [movedR, hf1, hf2, hI₁.1 f]
  · intro k hk1 hk2 hk3
    by_cases hk4 : k = cnt
    · subst hk4; simp [movedR, hct₁, hct, hcnt₁, hcnt]
    by_cases hk5 : k = ctmp
    · subst hk5; simp [movedR, Ne.symm h15, hct]
    simp [movedR, hk4, hk5, hoth₁ k hk1 hk4 hk5 hk2 hk3]

/-- `mergeIdx_exec` on routed sources: if `srcs d` holds `blocksIdx l B nb code i₀ d` (the
records of `l` with code `d`, in forward order) on top of `rest d`, then `dst` gains `l.reverse`
and each source is left with `rest d`. -/
theorem mergeIdx_exec_blocks [NeZero nr] (srcs : Fin nd → Fin T) (dst ctr tmp cnt ctmp : Fin T)
    (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ ℕ) (st : Fin T) (C : CAuto A nr nd)
    (h : IdxLayout cf len L rs tmps rsrc st (mergeRegs srcs dst ctr tmp cnt ctmp))
    (hreg : [dst, ctr, tmp, cnt, ctmp].Nodup) (hsrcs : ∀ d, srcs d ∉ [dst, ctr, tmp, cnt, ctmp])
    (hinj : Function.Injective srcs) {l c kk : List (Fin (A + 4))} {nb B i₀ : ℕ}
    (hl : l.length = nb * B) (hcB : c.length = B) (hk : kk.length = nb)
    (rest : Fin nd → List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hs : ∀ d, S.R (srcs d) = blocksIdx l B nb (idxCode C L len rsrc) i₀ d ++ rest d)
    (hc : S.R ctr = c) (ht : S.R tmp = []) (hcnt : S.R cnt = kk) (hct : S.R ctmp = [])
    (hI : IdxState cf len L rs tmps rsrc S.R i₀) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      Exec body (mergeIdx srcs dst ctr tmp cnt ctmp cf rs tmps st C) (mk v S)
        (nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 15) + 4) (mk v' { S with R := R' }) ∧
      R' dst = l.reverse ++ S.R dst ∧ (∀ d, R' (srcs d) = rest d) ∧
      (∀ f, R' (cf f) = binSyms (len f) (digit len f (i₀ + nb))) ∧
      ∀ k, k ≠ dst → (∀ d, srcs d ≠ k) → (∀ f, cf f ≠ k) → R' k = S.R k := by
  have hrt := mergeIdxList_blocksIdx B (idxCode C L len rsrc) nb i₀ l rest hl
  obtain ⟨v', R', hu, he, hdst, hsrc, hcf, hoth⟩ :=
    mergeIdx_exec body srcs dst ctr tmp cnt ctmp cf len L rs tmps rsrc st C h hreg hsrcs hinj hcB hk
      (fun d => blocksIdx l B nb (idxCode C L len rsrc) i₀ d ++ rest d)
      (fun d => by rw [List.length_append, length_blocksIdx _ _ _ _ _ _ hl]; omega)
      v S hs hc ht hcnt hct hI
  rw [hrt] at hdst hsrc
  exact ⟨v', R', hu, he, hdst, hsrc, hcf, hoth⟩

/-- The step count of `mergeIdx_exec` in the form
`nb * (4 * B + c * (L * (nr + 1) + ∑ f, len f + nf) + c') + c''`, with `c = 6`, `c' = 15`,
`c'' = 4`. -/
lemma mergeIdx_steps_le (nb B L : ℕ) (len : Fin nf → ℕ) :
    nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 15) + 4 ≤
      nb * (4 * B + 6 * (L * (nr + 1) + ∑ f, len f + nf) + 15) + 4 := by
  have : L ≤ L * (nr + 1) := Nat.le_mul_of_pos_right L (by omega)
  have : 4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 15 ≤
      4 * B + 6 * (L * (nr + 1) + ∑ f, len f + nf) + 15 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left nb this) 4

end IntegerMultBounds.MathlibTM2.Host
