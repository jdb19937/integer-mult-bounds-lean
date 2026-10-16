module

public import IntegerMultBounds.MathlibTM2.Fast.CMul

/-!
# Complex fixed-point products on coefficient streams

A coefficient stream of `l : List GaussianInt` is `cstream A w l = l.flatMap (csyms A w)`: the
coefficients in order, the first on top, each as `w` pair symbols least significant first.

The stream programs are generic in the one-coefficient program `one` through its contract
`OneSpec one ok g w p c`: from every ready register file with coefficients `x`, `y` on top of `xs`,
`ys` (`ok x y`), `one` pops both, pushes their symbols onto `xsv`, `ysv` and pushes `g x y` onto
`acc`, within `c` steps. `cmulOne` meets it with `g x y = tdivN p (x y)` (`cmulOne_spec`), and so
does `rmulOne` for real second factors (`rmulOne_spec`).

* `cmulBlock one`: repeat `one` while `ys` is nonempty, then move `ysv` back onto `ys`.
  `block_runs`: for pairs `zs`, `xs` holding the first factors followed by any `rx`, `ys` holding
  the second factors and `ysv` empty, the result is `blockSt`: `xs = rx`, `ys` restored, the first
  factors' symbols on `xsv`, the results on `acc` (reversed), within
  `|zs| (c + 2 w + 2) + 4` steps.
* `cmulStream one`: `cmulBlock one`, then `acc` onto `out` and `xsv` onto `xs`. `stream_runs`:
  for `xs`, `ys` of equal length `n` (`xsv`, `ysv`, `acc` empty), `out` gains the stream of
  `zipWith g xs ys` on top, and every other register ends as it started, within
  `n (c + 6 w + 2) + 8` steps.
* `cmulTable one`: repeat `cmulBlock one` while `xs` is nonempty, then the same two moves.
  `table_runs`: for `xs = blocks.flatten`, every block of the length `L ≥ 1` of the table `ts` on
  `ys`, `out` gains the stream of `blocks.flatMap (zipWith g · ts)` on top: coefficient `i` of each
  block is multiplied by table entry `i` (`tableOut_getElem`: output `k` is `g xs[k] ts[k % L]`).
  Every other register ends as it started, within `n (c + 6 w + 8) + 6` steps, `n = |xs|`.

`cmulStream_runs`, `cmulTable_runs`: the instances for `cmulOne` with `g x y = tdivN p (x y)` and
`c = cmulCost T w`; `rmulStream_runs`, `rmulTable_runs`: for `rmulOne` and real second factors.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Schoenhage.Schedule (topN topN_facts)

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

/-- The stream of a list of coefficients. -/
def cstream (A w : ℕ) (l : List GaussianInt) : List (Fin (A + 4)) := l.flatMap (csyms A w)

@[simp] lemma cstream_nil {A w : ℕ} : cstream A w [] = [] := rfl

@[simp] lemma cstream_cons {A w : ℕ} (x : GaussianInt) (l : List GaussianInt) :
    cstream A w (x :: l) = csyms A w x ++ cstream A w l := by simp [cstream]

@[simp] lemma cstream_append {A w : ℕ} (l₁ l₂ : List GaussianInt) :
    cstream A w (l₁ ++ l₂) = cstream A w l₁ ++ cstream A w l₂ := by simp [cstream]

@[simp] lemma length_cstream {A w : ℕ} (l : List GaussianInt) : (cstream A w l).length = l.length * w := by
  induction l with
  | nil => simp [cstream]
  | cons x l ih => rw [cstream_cons, List.length_append, ih]; simp [csyms]; ring

lemma csyms_ne_nil {A w : ℕ} (hw : 1 ≤ w) (x : GaussianInt) : csyms A w x ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [csyms] at this
  omega

lemma map_zip_eq {α β γ : Type} (g : α → β → γ) (l : List α) (m : List β) :
    ((l.zip m).map fun z => g z.1 z.2) = List.zipWith g l m := by
  rw [List.map_zip_eq_zipWith]; rfl

lemma cstream_ne_nil {A w : ℕ} (hw : 1 ≤ w) {x : GaussianInt} {l : List GaussianInt} :
    cstream A w (x :: l) ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [length_cstream] at this
  simp at this
  omega

section Streams

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {cr : CR → Fin T}
  {ι : Fin 64 → Fin T}

variable (body cr ι) in
/-- The contract of a one-coefficient product `one`: result `g x y` for `ok x y`, within `c`
steps. -/
def OneSpec (one : Pr P T Q A U) (ok : GaussianInt → GaussianInt → Prop)
    (g : GaussianInt → GaussianInt → GaussianInt) (w p c : ℕ) : Prop :=
  ∀ (ρ : CR → List (Fin (A + 4))) (x y : GaussianInt) (rx ry : List (Fin (A + 4))),
    Ready ρ w p → ok x y → ρ .xs = csyms A w x ++ rx → ρ .ys = csyms A w y ++ ry →
      CRuns body cr ι one ρ (oneSt ρ w x y rx ry (g x y)) c

/-! ### Blocks -/

/-- Repeat `one` while `ys` is nonempty, then move `ysv` back onto `ys`. -/
def cmulBlock (cr : CR → Fin T) (one : Pr P T Q A U) : Pr P T Q A U :=
  .seq (cwhileP (cr .ys) one) (moveR (cr .ysv) (cr .ys) id)

/-- The register file inside a block: pairs `rem` remain, pairs `done` are processed. -/
def blockLoopSt (ρ : CR → List (Fin (A + 4))) (w : ℕ)
    (g : GaussianInt → GaussianInt → GaussianInt) (rx : List (Fin (A + 4)))
    (rem done : List (GaussianInt × GaussianInt)) : CR → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update ρ
    .xs (cstream A w (rem.map Prod.fst) ++ rx)) .ys (cstream A w (rem.map Prod.snd)))
    .xsv ((cstream A w (done.map Prod.fst)).reverse ++ ρ .xsv))
    .ysv ((cstream A w (done.map Prod.snd)).reverse ++ ρ .ysv))
    .acc ((cstream A w (done.map fun z => g z.1 z.2)).reverse ++ ρ .acc)

/-- The register file after a block of pairs `zs`. -/
def blockSt (ρ : CR → List (Fin (A + 4))) (w : ℕ) (g : GaussianInt → GaussianInt → GaussianInt)
    (rx : List (Fin (A + 4))) (zs : List (GaussianInt × GaussianInt)) : CR → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update ρ .xs rx)
    .xsv ((cstream A w (zs.map Prod.fst)).reverse ++ ρ .xsv))
    .acc ((cstream A w (zs.map fun z => g z.1 z.2)).reverse ++ ρ .acc)

theorem block_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    {one : Pr P T Q A U} {ok : GaussianInt → GaussianInt → Prop}
    {g : GaussianInt → GaussianInt → GaussianInt} {w p c : ℕ}
    (hone : OneSpec body cr ι one ok g w p c) (hw : 1 ≤ w)
    {ρ : CR → List (Fin (A + 4))} (hr : Ready ρ w p) (zs : List (GaussianInt × GaussianInt))
    (hok : ∀ z ∈ zs, ok z.1 z.2) {rx : List (Fin (A + 4))}
    (hx : ρ .xs = cstream A w (zs.map Prod.fst) ++ rx) (hy : ρ .ys = cstream A w (zs.map Prod.snd))
    (hsv : ρ .ysv = []) :
    CRuns body cr ι (cmulBlock cr one) ρ (blockSt ρ w g rx zs) (zs.length * (c + 2 * w + 2) + 4) := by
  have hrst : ∀ rem done, Ready (blockLoopSt ρ w g rx rem done) w p := fun rem done =>
    ((((hr.update .xs (by simp) _).update .ys (by simp) _).update .xsv (by simp) _).update .ysv
      (by simp) _).update .acc (by simp) _
  have hstep : ∀ (a : GaussianInt × GaussianInt) rest done, ok a.1 a.2 →
      CRuns body cr ι one (blockLoopSt ρ w g rx (a :: rest) done)
        (blockLoopSt ρ w g rx rest (done ++ [a])) c := by
    intro a rest done ha
    refine (hone _ a.1 a.2 (cstream A w (rest.map Prod.fst) ++ rx) (cstream A w (rest.map Prod.snd))
      (hrst _ _) ha (by simp [blockLoopSt]) (by simp [blockLoopSt])).congr ?_
    funext r
    cases r <;> simp [blockLoopSt, oneSt, opSt]
  have hloop := cwhileP_runs hdisj .ys one (fun a => ok a.1 a.2) (blockLoopSt ρ w g rx) c hstep
    (fun a rest done _ => by simp [blockLoopSt, csyms_ne_nil hw])
    (fun done => by simp [blockLoopSt]) zs [] hok
  have h0 : blockLoopSt ρ w g rx zs [] = ρ := by
    funext r
    cases r <;> simp [blockLoopSt, hx, hy]
  rw [h0] at hloop
  have hmv := moveR_runs (body := body) (ι := ι) hcr (a := .ysv) (b := .ys) (by decide)
    (ρ := blockLoopSt ρ w g rx [] zs) (n := zs.length * w) (by simp [blockLoopSt, hsv])
  refine ((CRuns.seq hdisj hloop hmv).congr ?_).mono ?_
  · funext r
    cases r <;> simp [blockLoopSt, blockSt, hsv, hy]
  · nlinarith

/-! ### Streams -/

/-- Multiply two aligned streams; results onto `out`, `xs` restored. -/
def cmulStream (cr : CR → Fin T) (one : Pr P T Q A U) : Pr P T Q A U :=
  .seq (cmulBlock cr one) (.seq (moveR (cr .acc) (cr .out) id) (moveR (cr .xsv) (cr .xs) id))

theorem stream_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    {one : Pr P T Q A U} {ok : GaussianInt → GaussianInt → Prop}
    {g : GaussianInt → GaussianInt → GaussianInt} {w p c : ℕ}
    (hone : OneSpec body cr ι one ok g w p c) (hw : 1 ≤ w)
    {ρ : CR → List (Fin (A + 4))} (hr : Ready ρ w p) (xs ys : List GaussianInt)
    (hlen : xs.length = ys.length) (hok : ∀ z ∈ xs.zip ys, ok z.1 z.2)
    (hX : ρ .xs = cstream A w xs) (hY : ρ .ys = cstream A w ys) (hxsv : ρ .xsv = [])
    (hysv : ρ .ysv = []) (hacc : ρ .acc = []) :
    CRuns body cr ι (cmulStream cr one) ρ
      (Function.update ρ .out (cstream A w (List.zipWith g xs ys) ++ ρ .out))
      (xs.length * (c + 6 * w + 2) + 8) := by
  have h1 : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by omega)
  have h2 : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by omega)
  have h3 : ((xs.zip ys).map fun z => g z.1 z.2) = List.zipWith g xs ys := map_zip_eq g xs ys
  have hb := block_runs hcr hdisj hone hw hr (xs.zip ys) hok (rx := [])
    (by rw [h1, hX, List.append_nil]) (by rw [h2, hY]) hysv
  have hm1 := moveR_runs (body := body) (ι := ι) hcr (a := .acc) (b := .out) (by decide)
    (ρ := blockSt ρ w g [] (xs.zip ys)) (n := xs.length * w)
    (by simp [blockSt, hacc, h3, hlen])
  have hm2 := moveR_runs (body := body) (ι := ι) hcr (a := .xsv) (b := .xs) (by decide)
    (ρ := Function.update (Function.update (blockSt ρ w g [] (xs.zip ys)) .acc [])
      .out ((blockSt ρ w g [] (xs.zip ys) .acc).reverse ++ blockSt ρ w g [] (xs.zip ys) .out))
    (n := xs.length * w) (by simp [blockSt, hxsv, h1])
  refine ((CRuns.seq hdisj hb (CRuns.seq hdisj hm1 hm2)).congr ?_).mono ?_
  · funext r
    cases r <;> simp [blockSt, hxsv, hacc, hX, h1, h3]
  · simp only [List.length_zip, hlen, Nat.min_self]
    nlinarith

/-! ### Tables -/

/-- Multiply every block of `|ys|` consecutive coefficients of `xs` by the table on `ys`; results
onto `out`, `xs` restored. -/
def cmulTable (cr : CR → Fin T) (one : Pr P T Q A U) : Pr P T Q A U :=
  .seq (cwhileP (cr .xs) (cmulBlock cr one))
    (.seq (moveR (cr .acc) (cr .out) id) (moveR (cr .xsv) (cr .xs) id))

/-- The results of a table product, block by block. -/
def tableOut (g : GaussianInt → GaussianInt → GaussianInt) (blocks : List (List GaussianInt))
    (ts : List GaussianInt) : List GaussianInt :=
  blocks.flatMap fun b => List.zipWith g b ts

lemma length_flatten_const {α : Type} {L : ℕ} : ∀ (blocks : List (List α)),
    (∀ b ∈ blocks, b.length = L) → blocks.flatten.length = blocks.length * L
  | [], _ => by simp
  | b :: bs, h => by
      rw [List.flatten_cons, List.length_append, h b (by simp),
        length_flatten_const bs (fun b' hb' => h b' (by simp [hb'])), List.length_cons]
      ring

lemma length_tableOut (g : GaussianInt → GaussianInt → GaussianInt) :
    ∀ (blocks : List (List GaussianInt)) (ts : List GaussianInt),
      (∀ b ∈ blocks, b.length = ts.length) →
        (tableOut g blocks ts).length = blocks.length * ts.length
  | [], _, _ => by simp [tableOut]
  | b :: bs, ts, h => by
      have := length_tableOut g bs ts (fun b' hb' => h b' (by simp [hb']))
      simp only [tableOut, List.flatMap_cons, List.length_append, List.length_zipWith,
        h b (by simp), Nat.min_self, List.length_cons] at this ⊢
      rw [this]; ring

/-- Indexing a concatenation of pieces of length `L`. -/
lemma getElem_flatMap_len {α β : Type} (F : α → List β) (L : ℕ) :
    ∀ (l : List α) (hF : ∀ x ∈ l, (F x).length = L) (j i : ℕ) (hj : j < l.length) (hi : i < L)
      (h : L * j + i < (l.flatMap F).length),
      (l.flatMap F)[L * j + i] = (F l[j])[i]'(by rw [hF _ (List.getElem_mem hj)]; exact hi)
  | [], _, j, _, hj, _, _ => absurd hj (by simp)
  | x :: l, hF, j, i, hj, hi, h => by
      have hx : (F x).length = L := hF x (by simp)
      cases j with
      | zero =>
          simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
          rw [List.getElem_append_left (by omega)]
      | succ j =>
          have hj' : j < l.length := by simpa using hj
          have h' : L * j + i < (l.flatMap F).length := by
            simp only [List.flatMap_cons, List.length_append, hx] at h
            rw [Nat.mul_succ] at h; omega
          simp only [List.flatMap_cons, List.getElem_cons_succ]
          rw [List.getElem_append_right (by rw [hx, Nat.mul_succ]; omega)]
          have e : L * (j + 1) + i - (F x).length = L * j + i := by rw [hx, Nat.mul_succ]; omega
          simp only [e]
          exact getElem_flatMap_len F L l (fun y hy => hF y (by simp [hy])) j i hj' hi h'

/-- The register file of the block loop: blocks `rem` remain, blocks `done` are processed. -/
def tableLoopSt (ρ : CR → List (Fin (A + 4))) (w : ℕ)
    (g : GaussianInt → GaussianInt → GaussianInt) (ts : List GaussianInt)
    (rem done : List (List GaussianInt)) : CR → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update ρ .xs (cstream A w rem.flatten))
    .xsv ((cstream A w done.flatten).reverse ++ ρ .xsv))
    .acc ((cstream A w (tableOut g done ts)).reverse ++ ρ .acc)

theorem table_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    {one : Pr P T Q A U} {ok : GaussianInt → GaussianInt → Prop}
    {g : GaussianInt → GaussianInt → GaussianInt} {w p c : ℕ}
    (hone : OneSpec body cr ι one ok g w p c) (hw : 1 ≤ w)
    {ρ : CR → List (Fin (A + 4))} (hr : Ready ρ w p) (blocks : List (List GaussianInt))
    (ts : List GaussianInt) (hL : 1 ≤ ts.length) (hlen : ∀ b ∈ blocks, b.length = ts.length)
    (hok : ∀ b ∈ blocks, ∀ z ∈ b.zip ts, ok z.1 z.2)
    (hX : ρ .xs = cstream A w blocks.flatten) (hY : ρ .ys = cstream A w ts)
    (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = []) :
    CRuns body cr ι (cmulTable cr one) ρ
      (Function.update ρ .out (cstream A w (tableOut g blocks ts) ++ ρ .out))
      (blocks.flatten.length * (c + 6 * w + 8) + 6) := by
  set st := tableLoopSt ρ w g ts with hst
  have hstep : ∀ (b : List GaussianInt) rest done,
      (b.length = ts.length ∧ ∀ z ∈ b.zip ts, ok z.1 z.2) →
      CRuns body cr ι (cmulBlock cr one) (st (b :: rest) done) (st rest (done ++ [b]))
        (ts.length * (c + 2 * w + 2) + 4) := by
    intro b rest done ⟨hbL, hbok⟩
    have h1 : (b.zip ts).map Prod.fst = b := List.map_fst_zip (by omega)
    have h2 : (b.zip ts).map Prod.snd = ts := List.map_snd_zip (by omega)
    have hr' : Ready (st (b :: rest) done) w p :=
      (((hr.update .xs (by simp) _).update .xsv (by simp) _).update .acc (by simp) _)
    have hb := block_runs hcr hdisj hone hw hr' (b.zip ts) hbok
      (rx := cstream A w rest.flatten)
      (by rw [h1]; simp [st, tableLoopSt, cstream_append])
      (by rw [h2]; simp [st, tableLoopSt, hY]) (by simp [st, tableLoopSt, hysv])
    have hzl : (b.zip ts).length = ts.length := by simp [hbL]
    rw [hzl] at hb
    refine hb.congr ?_
    funext r
    cases r <;> simp [st, tableLoopSt, blockSt, h1, tableOut, map_zip_eq]
  have hloop := cwhileP_runs hdisj .xs (cmulBlock cr one)
    (fun b => b.length = ts.length ∧ ∀ z ∈ b.zip ts, ok z.1 z.2) st _ hstep
    (fun b rest done hb => by
      obtain ⟨x, b', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega :
        0 < b.length))
      simp only [st, tableLoopSt, Function.update_apply, ite_true, List.flatten_cons, List.cons_append]
      exact cstream_ne_nil hw)
    (fun done => by simp [st, tableLoopSt]) blocks [] (fun b hb => ⟨hlen b hb, hok b hb⟩)
  have hflat := length_flatten_const blocks hlen
  have hout := length_tableOut g blocks ts hlen
  have h0 : st blocks [] = ρ := by
    funext r
    cases r <;> simp [st, tableLoopSt, hX, hxsv, hacc, tableOut]
  rw [h0, List.nil_append] at hloop
  have hm1 := moveR_runs (body := body) (ι := ι) hcr (a := .acc) (b := .out) (by decide)
    (ρ := st [] blocks) (n := blocks.length * ts.length * w)
    (by simp [st, tableLoopSt, hacc, hout])
  have hm2 := moveR_runs (body := body) (ι := ι) hcr (a := .xsv) (b := .xs) (by decide)
    (ρ := Function.update (Function.update (st [] blocks) .acc [])
      .out ((st [] blocks .acc).reverse ++ st [] blocks .out))
    (n := blocks.length * ts.length * w) (by simp [st, tableLoopSt, hxsv, hflat])
  refine ((CRuns.seq hdisj hloop (CRuns.seq hdisj hm1 hm2)).congr ?_).mono ?_
  · funext r
    cases r <;> simp [st, tableLoopSt, hX, hxsv, hacc]
  · rw [hflat]
    have hB : blocks.length ≤ blocks.length * ts.length := Nat.le_mul_of_pos_right _ hL
    nlinarith

/-- The results of a table product in index form: output `k` is `g xs[k] ts[k % L]`. -/
theorem tableOut_getElem (g : GaussianInt → GaussianInt → GaussianInt)
    (blocks : List (List GaussianInt)) (ts : List GaussianInt) (hL : 1 ≤ ts.length)
    (hlen : ∀ b ∈ blocks, b.length = ts.length) (k : ℕ) (hk : k < blocks.flatten.length) :
    (tableOut g blocks ts)[k]'(by rw [length_tableOut g blocks ts hlen,
        ← length_flatten_const blocks hlen]; exact hk) =
      g (blocks.flatten[k]) (ts[k % ts.length]'(Nat.mod_lt _ (by omega))) := by
  have hflat := length_flatten_const blocks hlen
  have hout := length_tableOut g blocks ts hlen
  obtain ⟨j, i, hj, hi, rfl⟩ : ∃ j i, j < blocks.length ∧ i < ts.length ∧
      k = ts.length * j + i := by
    refine ⟨k / ts.length, k % ts.length, ?_, Nat.mod_lt _ (by omega), (Nat.div_add_mod k _).symm⟩
    rw [hflat] at hk
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
  have e1 := getElem_flatMap_len (fun b => List.zipWith g b ts) ts.length blocks
    (fun b hb => by simp [hlen b hb]) j i hj hi (by
      simp only [tableOut] at hout; rw [hout]; rw [hflat] at hk; exact hk)
  have e2 := getElem_flatMap_len id ts.length blocks (fun b hb => by simp [hlen b hb])
    j i hj hi (by simpa using hk)
  simp only [List.flatMap_id] at e2
  have hmod : (ts.length * j + i) % ts.length = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  simp only [tableOut, hmod]
  rw [e1, List.getElem_zipWith]
  congr 1
  exact e2.symm

/-! ### Instances: the complex and the real-weight product -/

theorem cmulOne_spec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) {w p : ℕ}
    (hw : 1 ≤ w) (hp : p ≤ w) :
    OneSpec body cr ι (cmulOne ι hι hT hQ cr) (fun x y => Fits w x ∧ Fits w y)
      (fun x y => tdivN p (x * y)) w p (cmulCost T w) :=
  fun _ _ _ _ _ hr hok hx hy => cmulOne_runs hcr hdisj hι hT hQ hA hr hw hp hok.1 hok.2 hx hy

theorem rmulOne_spec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) {w p : ℕ}
    (hw : 1 ≤ w) (hp : p ≤ w) :
    OneSpec body cr ι (rmulOne ι hι hT hQ cr) (fun x y => Fits w x ∧ Fits w y ∧ y.im = 0)
      (fun x y => tdivN p (x * y)) w p (rmulCost T w) :=
  fun _ _ _ _ _ hr hok hx hy =>
    rmulOne_runs hcr hdisj hι hT hQ hA hr hw hp hok.1 hok.2.1 hok.2.2 hx hy

/-- **Complex fixed-point products of aligned streams.** `xs` and `ys` hold the streams of
`xs`, `ys` (equal length `n`, all coefficients fitting `w` bits), `xsv`, `ysv`, `acc` are empty
and the register file is ready. Afterwards `out` gains the stream of `red w (tdivN p (xᵢ yᵢ))` on
top (first coefficient on top), every other register is as before (`xs` and `ys` restored), within
`n (cmulCost T w + 6 w + 2) + 8` steps. -/
theorem cmulStream_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    (xs ys : List GaussianInt) (hlen : xs.length = ys.length) (hfx : ∀ x ∈ xs, Fits w x)
    (hfy : ∀ y ∈ ys, Fits w y) (hX : ρ .xs = cstream A w xs) (hY : ρ .ys = cstream A w ys)
    (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = []) :
    CRuns body cr ι (cmulStream cr (cmulOne ι hι hT hQ cr)) ρ
      (Function.update ρ .out
        (cstream A w (List.zipWith (fun x y => tdivN p (x * y)) xs ys) ++ ρ .out))
      (xs.length * (cmulCost T w + 6 * w + 2) + 8) :=
  stream_runs hcr hdisj (cmulOne_spec hcr hdisj hι hT hQ hA hw hp) hw hr xs ys hlen
    (fun _ hz => ⟨hfx _ (List.of_mem_zip hz).1, hfy _ (List.of_mem_zip hz).2⟩) hX hY hxsv hysv
    hacc

/-- **Complex fixed-point products against a table.** `xs` holds the stream of
`blocks.flatten`, every block of the length `L ≥ 1` of the table `ts` held on `ys`; coefficient
`i` of every block is multiplied by table entry `i` (`tableOut_getElem`: output `k` is
`red w (tdivN p (xs[k] ts[k % L]))`). Afterwards `out` gains the result stream on top, every
other register is as before, within `n (cmulCost T w + 6 w + 8) + 6` steps, `n = |xs|`. -/
theorem cmulTable_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    (blocks : List (List GaussianInt)) (ts : List GaussianInt) (hL : 1 ≤ ts.length)
    (hlen : ∀ b ∈ blocks, b.length = ts.length) (hfx : ∀ x ∈ blocks.flatten, Fits w x)
    (hft : ∀ t ∈ ts, Fits w t) (hX : ρ .xs = cstream A w blocks.flatten)
    (hY : ρ .ys = cstream A w ts) (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = []) :
    CRuns body cr ι (cmulTable cr (cmulOne ι hι hT hQ cr)) ρ
      (Function.update ρ .out
        (cstream A w (tableOut (fun x y => tdivN p (x * y)) blocks ts) ++ ρ .out))
      (blocks.flatten.length * (cmulCost T w + 6 * w + 8) + 6) :=
  table_runs hcr hdisj (cmulOne_spec hcr hdisj hι hT hQ hA hw hp) hw hr blocks ts hL hlen
    (fun b hb _ hz => ⟨hfx _ (List.mem_flatten.2 ⟨b, hb, (List.of_mem_zip hz).1⟩),
      hft _ (List.of_mem_zip hz).2⟩) hX hY hxsv hysv hacc

/-- **One coefficient pair, operands restored.** `xs`, `ys` hold exactly the coefficients
`coeffSyms A w (red w N₁)`, `coeffSyms A w (red w N₂)`; afterwards `out` gains
`coeffSyms A w (red w (tdivN p (N₁ N₂)))` on top (least significant pair first) and every other
register is as before, within `cmulCost T w + 6 w + 10` steps. -/
theorem cmulPair_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    {N₁ N₂ : GaussianInt} (h₁ : Fits w N₁) (h₂ : Fits w N₂) (hX : ρ .xs = csyms A w N₁)
    (hY : ρ .ys = csyms A w N₂) (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = []) :
    CRuns body cr ι (cmulStream cr (cmulOne ι hι hT hQ cr)) ρ
      (Function.update ρ .out (csyms A w (tdivN p (N₁ * N₂)) ++ ρ .out))
      (cmulCost T w + 6 * w + 10) := by
  have H := cmulStream_runs (body := body) hcr hdisj hι hT hQ hA hr hw hp [N₁] [N₂] rfl (by simpa using h₁)
    (by simpa using h₂) (by simp [hX]) (by simp [hY]) hxsv hysv hacc
  refine (H.congr ?_).mono (by simp)
  simp

/-- `cmulStream_runs` for real second factors with `rmulOne` (two products per coefficient). -/
theorem rmulStream_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    (xs ys : List GaussianInt) (hlen : xs.length = ys.length) (hfx : ∀ x ∈ xs, Fits w x)
    (hfy : ∀ y ∈ ys, Fits w y ∧ y.im = 0) (hX : ρ .xs = cstream A w xs)
    (hY : ρ .ys = cstream A w ys) (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = []) :
    CRuns body cr ι (cmulStream cr (rmulOne ι hι hT hQ cr)) ρ
      (Function.update ρ .out
        (cstream A w (List.zipWith (fun x y => tdivN p (x * y)) xs ys) ++ ρ .out))
      (xs.length * (rmulCost T w + 6 * w + 2) + 8) :=
  stream_runs hcr hdisj (rmulOne_spec hcr hdisj hι hT hQ hA hw hp) hw hr xs ys hlen
    (fun _ hz => ⟨hfx _ (List.of_mem_zip hz).1, hfy _ (List.of_mem_zip hz).2⟩) hX hY hxsv hysv
    hacc

/-- `cmulTable_runs` for a real table with `rmulOne` (two products per coefficient). -/
theorem rmulTable_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    (blocks : List (List GaussianInt)) (ts : List GaussianInt) (hL : 1 ≤ ts.length)
    (hlen : ∀ b ∈ blocks, b.length = ts.length) (hfx : ∀ x ∈ blocks.flatten, Fits w x)
    (hft : ∀ t ∈ ts, Fits w t ∧ t.im = 0) (hX : ρ .xs = cstream A w blocks.flatten)
    (hY : ρ .ys = cstream A w ts) (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = []) :
    CRuns body cr ι (cmulTable cr (rmulOne ι hι hT hQ cr)) ρ
      (Function.update ρ .out
        (cstream A w (tableOut (fun x y => tdivN p (x * y)) blocks ts) ++ ρ .out))
      (blocks.flatten.length * (rmulCost T w + 6 * w + 8) + 6) :=
  table_runs hcr hdisj (rmulOne_spec hcr hdisj hι hT hQ hA hw hp) hw hr blocks ts hL hlen
    (fun b hb _ hz => ⟨hfx _ (List.mem_flatten.2 ⟨b, hb, (List.of_mem_zip hz).1⟩),
      hft _ (List.of_mem_zip hz).2⟩) hX hY hxsv hysv hacc

end Streams

end

end IntegerMultBounds.MathlibTM2.Fast
