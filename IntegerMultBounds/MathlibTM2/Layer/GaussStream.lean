module

public import IntegerMultBounds.MathlibTM2.Layer.GaussLin
public import IntegerMultBounds.MathlibTM2.Host.Auto

/-!
# Gaussian linear word automata on pair-symbol streams

`gaussAuto A g B swap` is a word automaton (`IntegerMultBounds.MathlibTM2.Host.Auto`) with `k` inputs and `l` outputs
that runs the column automaton `gstep g` of `GaussLin` on stack symbols. Its state symbol is the
mixed-radix code, base `2B + 1`, of the `2l` signed carries, each in `[-B, B]` (`encState`,
`decState`); the code fits in `Fin (A + 4)` when `(2B + 1)^(2l) ≤ A + 4`. A step decodes the state
and the input pair symbols (real and imaginary bit swapped when `swap`), takes one `gstep g`, and
emits one `pairSym` per output.

* `gaussAuto_runWord`, `gaussAuto_runWord_swap`: if `B ≥ Σᵢ (|aⱼᵢ| + |bⱼᵢ|)` for every output,
  the carries stay in `[-B, B]` (`gstep_bound`), so every reached state decodes to its carries and
  one word of `W` symbol columns of the residues `zs` yields the `W` symbol columns of
  `glin g zs` (of `glin g` on the swapped residues when `swap`), by `grun_correct`.
* `gaussAuto_exec`, `gaussAuto_exec_swap`: `autoWords` with `gaussAuto` on host registers holding
  the coefficient streams `(cs i).flatMap (coeffSyms A W)` of `n` coefficients each, in at most
  `n (5W + 6) + 2` steps. `arrSyms_eq_flatten` puts the stream of an array in this form.
* Instances: the kernel butterfly `GR.kernel2` (`kernel2_exec`), multiplication by `a + b i`
  (`mulG_exec`, `double_exec`, `mulI_exec`, `neg_exec`), and conjugation (`conj_exec`,
  `mulG_conj_exec`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.MathlibTM2.Host

/-! ### Carry codes -/

/-- Mixed-radix code, base `2B + 1`, of a list of carry pairs with parts in `[-B, B]`. -/
def encPairs (B : ℕ) : List (ℤ × ℤ) → ℕ
  | [] => 0
  | p :: ps => (p.1 + B).toNat + (2 * B + 1) * ((p.2 + B).toNat + (2 * B + 1) * encPairs B ps)

/-- The first `n` carry pairs of a mixed-radix code. -/
def decPairs (B : ℕ) : ℕ → ℕ → List (ℤ × ℤ)
  | 0, _ => []
  | n + 1, x =>
      (((x % (2 * B + 1) : ℕ) : ℤ) - B, ((x / (2 * B + 1) % (2 * B + 1) : ℕ) : ℤ) - B) ::
        decPairs B n (x / (2 * B + 1) / (2 * B + 1))

private lemma toNat_add_lt {B : ℕ} {a : ℤ} (ha : |a| ≤ B) : (a + B).toNat < 2 * B + 1 := by
  rw [abs_le] at ha; omega

private lemma toNat_add_cast {B : ℕ} {a : ℤ} (ha : |a| ≤ B) :
    (((a + B).toNat : ℕ) : ℤ) - B = a := by
  rw [abs_le] at ha; omega

lemma decPairs_encPairs (B : ℕ) : ∀ ps : List (ℤ × ℤ), (∀ p ∈ ps, |p.1| ≤ B ∧ |p.2| ≤ B) →
    decPairs B ps.length (encPairs B ps) = ps
  | [], _ => rfl
  | p :: ps, h => by
      have hp := h p List.mem_cons_self
      have ha := toNat_add_lt hp.1
      have hb := toNat_add_lt hp.2
      have hm : 0 < 2 * B + 1 := by omega
      set m := 2 * B + 1
      set a := (p.1 + B).toNat
      set b := (p.2 + B).toNat
      set e := encPairs B ps
      have h1 : (a + m * (b + m * e)) % m = a := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      have h2 : (a + m * (b + m * e)) / m = b + m * e := by
        rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt ha, zero_add]
      have h3 : (b + m * e) % m = b := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
      have h4 : (b + m * e) / m = e := by
        rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hb, zero_add]
      simp only [List.length_cons, encPairs, decPairs]
      rw [h1, h2, h3, h4, decPairs_encPairs B ps fun q hq => h q (List.mem_cons_of_mem _ hq),
        toNat_add_cast hp.1, toNat_add_cast hp.2]

lemma encPairs_lt (B : ℕ) : ∀ ps : List (ℤ × ℤ), (∀ p ∈ ps, |p.1| ≤ B ∧ |p.2| ≤ B) →
    encPairs B ps < (2 * B + 1) ^ (2 * ps.length)
  | [], _ => by simp [encPairs]
  | p :: ps, h => by
      have hp := h p List.mem_cons_self
      have ha := toNat_add_lt hp.1
      have hb := toNat_add_lt hp.2
      have he := encPairs_lt B ps fun q hq => h q (List.mem_cons_of_mem _ hq)
      simp only [encPairs, List.length_cons]
      set m := 2 * B + 1
      set a := (p.1 + B).toNat
      set b := (p.2 + B).toNat
      set e := encPairs B ps
      set M := m ^ (2 * ps.length)
      have hM : m ^ (2 * (ps.length + 1)) = m * (m * M) := by
        rw [show 2 * (ps.length + 1) = 2 * ps.length + 1 + 1 by ring, pow_succ, pow_succ]; ring
      rw [hM]
      have h1 : b + m * e + 1 ≤ m * M := by
        have : m * (e + 1) ≤ m * M := Nat.mul_le_mul_left _ he
        nlinarith
      have h2 : a + m * (b + m * e) + 1 ≤ m * (m * M) := by
        have : m * (b + m * e + 1) ≤ m * (m * M) := Nat.mul_le_mul_left _ h1
        nlinarith
      omega

variable {k l : ℕ}

/-- The state symbol of carries `c`, all parts in `[-B, B]`. -/
def encState (A B : ℕ) (c : Fin l → ℤ × ℤ) : Fin (A + 4) :=
  ⟨encPairs B (List.ofFn c) % (A + 4), Nat.mod_lt _ (by omega)⟩

/-- The carries of a state symbol. -/
def decState (B : ℕ) {A : ℕ} (s : Fin (A + 4)) : Fin l → ℤ × ℤ :=
  fun j => (decPairs B l s.val).getD j (0, 0)

/-- States round-trip when the carries lie in `[-B, B]` and `A + 4` covers all codes. -/
theorem decState_encState {A B : ℕ} (hR : (2 * B + 1) ^ (2 * l) ≤ A + 4) {c : Fin l → ℤ × ℤ}
    (hc : CarryLe (B : ℤ) c) : decState B (encState A B c) = c := by
  have hle : ∀ p ∈ List.ofFn c, |p.1| ≤ (B : ℤ) ∧ |p.2| ≤ (B : ℤ) := by
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact hc j
  have hlt := encPairs_lt B _ hle
  rw [List.length_ofFn] at hlt
  funext j
  simp only [decState, encState]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hlt hR)]
  have := decPairs_encPairs B _ hle
  rw [List.length_ofFn] at this
  rw [this]
  simp

/-! ### The automaton -/

/-- The bit pair of a pair symbol, real bit first; swapped when `swap`. -/
def pairOf (swap : Bool) {A : ℕ} (y : Fin (A + 4)) : Bool × Bool :=
  if swap then (pairIm y, pairRe y) else (pairRe y, pairIm y)

/-- A column of bit pairs as pair symbols. -/
def symCol (A : ℕ) {m : ℕ} (x : Fin m → Bool × Bool) : Fin m → Fin (A + 4) :=
  fun i => pairSym A (x i).1 (x i).2

/-- A column of bit pairs, every pair swapped when `swap`. -/
def swapCol (swap : Bool) {m : ℕ} (x : Fin m → Bool × Bool) : Fin m → Bool × Bool :=
  if swap then fun i => (x i).swap else x

lemma pairOf_symCol {A : ℕ} (hA : 4 ≤ A) (swap : Bool) {m : ℕ} (x : Fin m → Bool × Bool) :
    (fun i => pairOf swap (symCol A x i)) = swapCol swap x := by
  funext i
  cases swap <;> simp [pairOf, symCol, swapCol, pairRe_pairSym hA, pairIm_pairSym hA, Prod.swap]

/-- The Gaussian linear word automaton of `g`: the state symbol encodes the carries (parts in
`[-B, B]`), each step decodes the input symbols into bit pairs (swapped when `swap`), takes one
`gstep g` and emits one pair symbol per output. -/
def gaussAuto (A : ℕ) (g : Fin l → Fin k → ℤ × ℤ) (B : ℕ) (swap : Bool) : Auto A k l where
  init := encState A B fun _ : Fin l => ((0 : ℤ), (0 : ℤ))
  step s x :=
    let r := gstep g (decState B s) fun i => pairOf swap (x i)
    (encState A B r.1, symCol A r.2)

lemma carryLe_zero (B : ℕ) : CarryLe (B : ℤ) (fun _ : Fin l => ((0 : ℤ), (0 : ℤ))) :=
  fun _ => by simp

/-- From any state encoding carries in `[-B, B]`, the automaton runs `grun` on the decoded (and,
when `swap`, swapped) input columns. -/
theorem gaussAuto_runWord_grun {A B : ℕ} (hA : 4 ≤ A) {g : Fin l → Fin k → ℤ × ℤ}
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ (B : ℤ)) (hR : (2 * B + 1) ^ (2 * l) ≤ A + 4)
    (swap : Bool) :
    ∀ (xs : List (Fin k → Bool × Bool)) (c : Fin l → ℤ × ℤ), CarryLe (B : ℤ) c →
      (gaussAuto A g B swap).runWord (encState A B c) (xs.map (symCol A)) =
        (grun g c (xs.map (swapCol swap))).map (symCol A)
  | [], _, _ => rfl
  | x :: xs, c, hc => by
      simp only [List.map_cons, Auto.runWord, grun]
      have hs : (gaussAuto A g B swap).step (encState A B c) (symCol A x) =
          (encState A B (gstep g c (swapCol swap x)).1,
            symCol A (gstep g c (swapCol swap x)).2) := by
        simp only [gaussAuto, decState_encState hR hc, pairOf_symCol hA]
      rw [hs, gaussAuto_runWord_grun hA hB hR swap xs _ (gstep_bound g hB hc _)]

/-! ### Columns of coefficient symbols -/

section Syms

variable {W : ℕ}

/-- The `W` symbol columns of a family of coefficients: column `t` holds symbol `t` of every
coefficient. -/
def symCols (A : ℕ) (zs : Fin k → GR W) : List (Fin k → Fin (A + 4)) :=
  List.ofFn fun t : Fin W => fun i => (coeffSyms A W (zs i))[t]

lemma symCols_eq (A : ℕ) (zs : Fin k → GR W) : symCols A zs = (gcols zs).map (symCol A) := by
  simp [symCols, gcols, coeffSyms, List.map_ofFn, Function.comp_def]
  rfl

@[simp] lemma length_symCols (A : ℕ) (zs : Fin k → GR W) : (symCols A zs).length = W := by
  simp [symCols]

lemma symCols_map (A : ℕ) (zs : Fin k → GR W) (i : Fin k) :
    (symCols A zs).map (· i) = coeffSyms A W (zs i) := by
  simp [symCols, coeffSyms, List.map_ofFn, Function.comp_def]

/-- Real and imaginary parts swapped when `swap`. -/
def swapGR (swap : Bool) (z : GR W) : GR W := if swap then z.swap else z

@[simp] lemma swapGR_false (z : GR W) : swapGR false z = z := rfl

@[simp] lemma swapGR_true (z : GR W) : swapGR true z = z.swap := rfl

lemma gcols_swapCol (swap : Bool) (zs : Fin k → GR W) :
    (gcols zs).map (swapCol swap) = gcols fun i => swapGR swap (zs i) := by
  cases swap
  · have h : swapCol false = (id : (Fin k → Bool × Bool) → Fin k → Bool × Bool) := rfl
    simp [h, swapGR]
  · have h : swapCol true = fun (x : Fin k → Bool × Bool) i => (x i).swap := rfl
    simpa [h, swapGR] using gcols_swap zs

end Syms

section Run

variable {A B W : ℕ} {g : Fin l → Fin k → ℤ × ℤ}

/-- From its initial state, the automaton maps the symbol columns of the inputs (parts swapped
when `swap`) to the symbol columns of the outputs `glin g`. -/
theorem gaussAuto_runWord_gen (hA : 4 ≤ A)
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ (B : ℤ)) (hR : (2 * B + 1) ^ (2 * l) ≤ A + 4)
    (swap : Bool) (zs : Fin k → GR W) :
    (gaussAuto A g B swap).runWord (gaussAuto A g B swap).init (symCols A zs) =
      symCols A (glin g fun i => swapGR swap (zs i)) := by
  rw [symCols_eq, symCols_eq]
  have := gaussAuto_runWord_grun hA hB hR swap (gcols zs) _ (carryLe_zero B)
  rw [gcols_swapCol, grun_correct] at this
  exact this

/-- The automaton maps the symbol columns of `zs` to those of `glin g zs`. -/
theorem gaussAuto_runWord (hA : 4 ≤ A)
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ (B : ℤ)) (hR : (2 * B + 1) ^ (2 * l) ≤ A + 4)
    (zs : Fin k → GR W) :
    (gaussAuto A g B false).runWord (gaussAuto A g B false).init
        (List.ofFn fun t : Fin W => fun i => (coeffSyms A W (zs i))[t]) =
      List.ofFn fun t : Fin W => fun j => (coeffSyms A W (glin g zs j))[t] :=
  gaussAuto_runWord_gen hA hB hR false zs

/-- With `swap`, the automaton maps the symbol columns of `zs` to those of `glin g` applied to
the swapped residues. -/
theorem gaussAuto_runWord_swap (hA : 4 ≤ A)
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ (B : ℤ)) (hR : (2 * B + 1) ^ (2 * l) ≤ A + 4)
    (zs : Fin k → GR W) :
    (gaussAuto A g B true).runWord (gaussAuto A g B true).init
        (List.ofFn fun t : Fin W => fun i => (coeffSyms A W (zs i))[t]) =
      List.ofFn fun t : Fin W => fun j => (coeffSyms A W (glin g (fun i => (zs i).swap) j))[t] :=
  gaussAuto_runWord_gen hA hB hR true zs

end Run

/-! ### Streams of coefficients -/

section Words

variable {W n : ℕ}

/-- The words of a coefficient stream: word `c` is the symbol columns of coefficient `c` of every
input. -/
def gaussWords (A : ℕ) (zs : Fin n → Fin k → GR W) : List (List (Fin k → Fin (A + 4))) :=
  List.ofFn fun c => symCols A (zs c)

lemma length_gaussWords (A : ℕ) (zs : Fin n → Fin k → GR W) : (gaussWords A zs).length = n := by
  simp [gaussWords]

lemma gaussWords_length (A : ℕ) (zs : Fin n → Fin k → GR W) :
    ∀ w ∈ gaussWords A zs, w.length = W := by
  intro w hw
  obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hw
  simp

lemma stream_gaussWords (A : ℕ) (zs : Fin n → Fin k → GR W) (i : Fin k) :
    Auto.stream (gaussWords A zs) i = (List.ofFn fun c => zs c i).flatMap (coeffSyms A W) := by
  simp only [Auto.stream, gaussWords, List.flatMap_def, List.map_ofFn, Function.comp_def,
    symCols_map]

lemma outWords_gaussAuto {A B : ℕ} {g : Fin l → Fin k → ℤ × ℤ} (hA : 4 ≤ A)
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ (B : ℤ)) (hR : (2 * B + 1) ^ (2 * l) ≤ A + 4)
    (swap : Bool) (zs : Fin n → Fin k → GR W) (j : Fin l) :
    (gaussAuto A g B swap).outWords (gaussWords A zs) j =
      (List.ofFn fun c => glin g (fun i => swapGR swap (zs c i)) j).flatMap (coeffSyms A W) := by
  simp only [Auto.outWords, gaussWords, List.flatMap_def, List.map_ofFn, Function.comp_def,
    gaussAuto_runWord_gen hA hB hR, symCols_map]

/-- A list of length `n` is the `ofFn` of its entries. -/
private lemma ofFn_getElem_of_length {α : Type*} (L : List α) (h : L.length = n) :
    List.ofFn (fun c : Fin n => L[(c : ℕ)]'(by rw [h]; exact c.isLt)) = L := by
  apply List.ext_getElem (by simp [h])
  intro t _ _
  simp

/-- `arrSyms` is the coefficient symbol stream of the flattened array. -/
lemma arrSyms_eq_flatten (A W : ℕ) (arr : List (List (GR W))) :
    arrSyms A W arr = arr.flatten.flatMap (coeffSyms A W) := by
  induction arr with
  | nil => rfl
  | cons r rs ih =>
      simp only [arrSyms, recSyms, List.flatMap_cons, List.flatten_cons,
        List.flatMap_append] at ih ⊢
      rw [ih]

end Words

/-! ### Execution on host registers -/

section Exec

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- `autoWords` with `gaussAuto` on a coefficient matrix: input register `ins i` holds the
coefficients `zs c i` for `c < n`; output register `outs j` gains the coefficients of output `j`
reversed on top. -/
theorem gaussAuto_exec_gen [NeZero k] {ins : Fin k → Fin T} {outs : Fin l → Fin T}
    {st ctr tmp : Fin T} (h : AutoLayout ins outs st ctr tmp) {B W n : ℕ}
    {g : Fin l → Fin k → ℤ × ℤ} (hA : 4 ≤ A)
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ (B : ℤ)) (hR : (2 * B + 1) ^ (2 * l) ≤ A + 4)
    (swap : Bool) (hW : 1 ≤ W) {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W)
    (zs : Fin n → Fin k → GR W) (v : HS T Q A U) (S : Stacks T A) (hctr : S.R ctr = ctrs)
    (htmp : S.R tmp = [])
    (hin : ∀ i, S.R (ins i) = (List.ofFn fun c => zs c i).flatMap (coeffSyms A W)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ n * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp (gaussAuto A g B swap)) (mk v S) m
        (mk v' { S with R := autoRegs S.R ins outs (fun j =>
          (List.ofFn fun c => glin g (fun i => swapGR swap (zs c i)) j).flatMap
            (coeffSyms A W)) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := autoWords_exec_words body h (gaussAuto A g B swap) hW hctrs
    (gaussWords A zs) (gaussWords_length A zs) v S hctr htmp
    (fun i => by rw [hin, stream_gaussWords])
  refine ⟨v', m, hu, by simpa [length_gaussWords] using hm, ?_⟩
  have hout : (gaussAuto A g B swap).outWords (gaussWords A zs) = fun j =>
      (List.ofFn fun c => glin g (fun i => swapGR swap (zs c i)) j).flatMap (coeffSyms A W) :=
    funext (outWords_gaussAuto hA hB hR swap zs)
  rwa [hout] at he

/-- `gaussAuto_exec_gen` on coefficient lists `cs i` of a common length `n`, swapping parts when
`swap`, with the resulting stacks spelled out. -/
theorem gaussAuto_exec_list [NeZero k] {ins : Fin k → Fin T} {outs : Fin l → Fin T}
    {st ctr tmp : Fin T} (h : AutoLayout ins outs st ctr tmp) {B W n : ℕ}
    {g : Fin l → Fin k → ℤ × ℤ} (hA : 4 ≤ A)
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ (B : ℤ)) (hR : (2 * B + 1) ^ (2 * l) ≤ A + 4)
    (swap : Bool) (hW : 1 ≤ W) {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W)
    (cs : Fin k → List (GR W)) (hcs : ∀ i, (cs i).length = n) (v : HS T Q A U) (S : Stacks T A)
    (hctr : S.R ctr = ctrs) (htmp : S.R tmp = [])
    (hin : ∀ i, S.R (ins i) = (cs i).flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ n * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp (gaussAuto A g B swap)) (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ (∀ i, S'.R (ins i) = []) ∧
      (∀ j, S'.R (outs j) =
        ((List.ofFn fun c : Fin n =>
          glin g (fun i => swapGR swap ((cs i)[(c : ℕ)]'(by rw [hcs i]; exact c.isLt))) j).flatMap
            (coeffSyms A W)).reverse ++ S.R (outs j)) ∧
      ∀ r, r ∉ Set.range ins → r ∉ Set.range outs → S'.R r = S.R r := by
  obtain ⟨v', m, hu, hm, he⟩ := gaussAuto_exec_gen body h hA hB hR swap hW hctrs
    (fun c i => (cs i)[(c : ℕ)]'(by rw [hcs i]; exact c.isLt)) v S hctr htmp
    (fun i => by rw [hin, ofFn_getElem_of_length (cs i) (hcs i)])
  exact ⟨v', m, _, hu, hm, he, rfl, rfl, rfl, fun i => autoRegs_ins h.ins_inj i,
    fun j => autoRegs_outs h.outs_inj h.ins_outs j, fun r h1 h2 => autoRegs_of_notMem h1 h2⟩

/-- **Gaussian linear automaton on host registers.** Input register `ins i` holds the
coefficients `cs i`, all of length `n`; each output register `outs j` gains the coefficients
`Σᵢ gⱼᵢ (cs i)[c]` (`c < n`) reversed on top; the inputs end empty and all other registers
(`ctr` and `tmp` included) end as they started. -/
theorem gaussAuto_exec [NeZero k] {ins : Fin k → Fin T} {outs : Fin l → Fin T}
    {st ctr tmp : Fin T} (h : AutoLayout ins outs st ctr tmp) {B W n : ℕ}
    {g : Fin l → Fin k → ℤ × ℤ} (hA : 4 ≤ A)
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ (B : ℤ)) (hR : (2 * B + 1) ^ (2 * l) ≤ A + 4)
    (hW : 1 ≤ W) {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W)
    (cs : Fin k → List (GR W)) (hcs : ∀ i, (cs i).length = n) (v : HS T Q A U) (S : Stacks T A)
    (hctr : S.R ctr = ctrs) (htmp : S.R tmp = [])
    (hin : ∀ i, S.R (ins i) = (cs i).flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ n * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp (gaussAuto A g B false)) (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ (∀ i, S'.R (ins i) = []) ∧
      (∀ j, S'.R (outs j) =
        ((List.ofFn fun c : Fin n =>
          glin g (fun i => (cs i)[(c : ℕ)]'(by rw [hcs i]; exact c.isLt)) j).flatMap
            (coeffSyms A W)).reverse ++ S.R (outs j)) ∧
      ∀ r, r ∉ Set.range ins → r ∉ Set.range outs → S'.R r = S.R r :=
  gaussAuto_exec_list body h hA hB hR false hW hctrs cs hcs v S hctr htmp hin

/-- `gaussAuto_exec` with real and imaginary parts of every input swapped. -/
theorem gaussAuto_exec_swap [NeZero k] {ins : Fin k → Fin T} {outs : Fin l → Fin T}
    {st ctr tmp : Fin T} (h : AutoLayout ins outs st ctr tmp) {B W n : ℕ}
    {g : Fin l → Fin k → ℤ × ℤ} (hA : 4 ≤ A)
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ (B : ℤ)) (hR : (2 * B + 1) ^ (2 * l) ≤ A + 4)
    (hW : 1 ≤ W) {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W)
    (cs : Fin k → List (GR W)) (hcs : ∀ i, (cs i).length = n) (v : HS T Q A U) (S : Stacks T A)
    (hctr : S.R ctr = ctrs) (htmp : S.R tmp = [])
    (hin : ∀ i, S.R (ins i) = (cs i).flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ n * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp (gaussAuto A g B true)) (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ (∀ i, S'.R (ins i) = []) ∧
      (∀ j, S'.R (outs j) =
        ((List.ofFn fun c : Fin n =>
          glin g (fun i => ((cs i)[(c : ℕ)]'(by rw [hcs i]; exact c.isLt)).swap) j).flatMap
            (coeffSyms A W)).reverse ++ S.R (outs j)) ∧
      ∀ r, r ∉ Set.range ins → r ∉ Set.range outs → S'.R r = S.R r :=
  gaussAuto_exec_list body h hA hB hR true hW hctrs cs hcs v S hctr htmp hin

end Exec

/-! ### Instances -/

section Instances

variable {W : ℕ}

lemma glin_kernel2 (u v : GR W) :
    glin gKernel2 ![u, v] = ![(GR.kernel2 u v).1, (GR.kernel2 u v).2] := by
  funext j
  rw [glin_eq_sum_mulG]
  fin_cases j <;> simp [gKernel2, GR.kernel2, Fin.sum_univ_two]

lemma glin_mulG (a b : ℤ) (z : GR W) : glin ![![(a, b)]] ![z] 0 = GR.mulG a b z := by
  rw [glin_eq_sum_mulG]
  simp

lemma glin_mulG_conj (a b : ℤ) (z : GR W) :
    glin ![![(b, -a)]] ![z.swap] 0 = GR.mulG a b (GR.conj z) := by
  rw [glin_mulG]
  simp only [GR.mulG, GR.conj, Prod.fst_swap, Prod.snd_swap, Prod.ext_iff]
  push_cast
  constructor <;> ring

lemma gaussBound_one (a b : ℤ) :
    ∀ j, ∑ i, (|((![![(a, b)]] : Fin 1 → Fin 1 → ℤ × ℤ) j i).1| +
      |((![![(a, b)]] : Fin 1 → Fin 1 → ℤ × ℤ) j i).2|) ≤ ((a.natAbs + b.natAbs : ℕ) : ℤ) := by
  intro j
  fin_cases j
  simp

end Instances

section ExecInstances

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- A one-input, one-output Gaussian automaton computing `f` coefficientwise. -/
theorem gaussAuto_exec_one {ins outs : Fin 1 → Fin T} {st ctr tmp : Fin T}
    (h : AutoLayout ins outs st ctr tmp) {B W : ℕ} {g : Fin 1 → Fin 1 → ℤ × ℤ} (hA : 4 ≤ A)
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ (B : ℤ)) (hR : (2 * B + 1) ^ 2 ≤ A + 4)
    (swap : Bool) (f : GR W → GR W) (hf : ∀ z, glin g ![swapGR swap z] 0 = f z) (hW : 1 ≤ W)
    {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W) (zs : List (GR W)) (v : HS T Q A U)
    (S : Stacks T A) (hctr : S.R ctr = ctrs) (htmp : S.R tmp = [])
    (hin : S.R (ins 0) = zs.flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ zs.length * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp (gaussAuto A g B swap)) (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R (ins 0) = [] ∧
      S'.R (outs 0) = ((zs.map f).flatMap (coeffSyms A W)).reverse ++ S.R (outs 0) ∧
      ∀ r, r ≠ ins 0 → r ≠ outs 0 → S'.R r = S.R r := by
  obtain ⟨v', m, S', hu, hm, he, hi, ho, hl, hins, houts, hoth⟩ :=
    gaussAuto_exec_list body h hA hB (by simpa using hR) swap hW hctrs (fun _ => zs)
      (fun _ => rfl) v S hctr htmp (fun i => by rw [Fin.fin_one_eq_zero i, hin])
  refine ⟨v', m, S', hu, hm, he, hi, ho, hl, hins 0, ?_, ?_⟩
  · rw [houts 0]
    congr 3
    apply List.ext_getElem (by simp)
    intro t _ _
    simp only [List.getElem_ofFn, List.getElem_map, ← hf]
    congr 2
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  · intro r h1 h2
    refine hoth r ?_ ?_
    · rintro ⟨i, rfl⟩; exact h1 (by rw [Fin.fin_one_eq_zero i])
    · rintro ⟨j, rfl⟩; exact h2 (by rw [Fin.fin_one_eq_zero j])

/-- Multiplication of every coefficient by the Gaussian integer `a + b i`. -/
theorem mulG_exec {ins outs : Fin 1 → Fin T} {st ctr tmp : Fin T}
    (h : AutoLayout ins outs st ctr tmp) {W : ℕ} (a b : ℤ) (hA : 4 ≤ A)
    (hR : (2 * (a.natAbs + b.natAbs) + 1) ^ 2 ≤ A + 4) (hW : 1 ≤ W)
    {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W) (zs : List (GR W)) (v : HS T Q A U)
    (S : Stacks T A) (hctr : S.R ctr = ctrs) (htmp : S.R tmp = [])
    (hin : S.R (ins 0) = zs.flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ zs.length * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp
        (gaussAuto A ![![(a, b)]] (a.natAbs + b.natAbs) false)) (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R (ins 0) = [] ∧
      S'.R (outs 0) =
        ((zs.map (GR.mulG a b)).flatMap (coeffSyms A W)).reverse ++ S.R (outs 0) ∧
      ∀ r, r ≠ ins 0 → r ≠ outs 0 → S'.R r = S.R r :=
  gaussAuto_exec_one body h hA (gaussBound_one a b) hR false (GR.mulG a b)
    (fun z => glin_mulG a b z) hW hctrs zs v S hctr htmp hin

/-- Doubling of every coefficient (`a + b i = 2`). -/
theorem double_exec {ins outs : Fin 1 → Fin T} {st ctr tmp : Fin T}
    (h : AutoLayout ins outs st ctr tmp) {W : ℕ} (hR : 5 ^ 2 ≤ A + 4) (hW : 1 ≤ W)
    {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W) (zs : List (GR W)) (v : HS T Q A U)
    (S : Stacks T A) (hctr : S.R ctr = ctrs) (htmp : S.R tmp = [])
    (hin : S.R (ins 0) = zs.flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ zs.length * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp (gaussAuto A ![![(2, 0)]] 2 false)) (mk v S) m
        (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R (ins 0) = [] ∧
      S'.R (outs 0) = ((zs.map fun z => z + z).flatMap (coeffSyms A W)).reverse ++ S.R (outs 0) ∧
      ∀ r, r ≠ ins 0 → r ≠ outs 0 → S'.R r = S.R r :=
  gaussAuto_exec_one body h (by norm_num at hR; omega) (gaussBound_one 2 0)
    (by norm_num at hR ⊢; omega) false
    (fun z => z + z) (fun z => by rw [glin_mulG]; simp [GR.mulG, Prod.ext_iff, two_mul])
    hW hctrs zs v S hctr htmp hin

/-- Multiplication of every coefficient by `i`. -/
theorem mulI_exec {ins outs : Fin 1 → Fin T} {st ctr tmp : Fin T}
    (h : AutoLayout ins outs st ctr tmp) {W : ℕ} (hR : 3 ^ 2 ≤ A + 4) (hW : 1 ≤ W)
    {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W) (zs : List (GR W)) (v : HS T Q A U)
    (S : Stacks T A) (hctr : S.R ctr = ctrs) (htmp : S.R tmp = [])
    (hin : S.R (ins 0) = zs.flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ zs.length * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp (gaussAuto A ![![(0, 1)]] 1 false)) (mk v S) m
        (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R (ins 0) = [] ∧
      S'.R (outs 0) = ((zs.map GR.mulI).flatMap (coeffSyms A W)).reverse ++ S.R (outs 0) ∧
      ∀ r, r ≠ ins 0 → r ≠ outs 0 → S'.R r = S.R r :=
  gaussAuto_exec_one body h (by norm_num at hR; omega) (gaussBound_one 0 1)
    (by norm_num at hR ⊢; omega) false GR.mulI
    (fun z => by rw [glin_mulG]; simp [GR.mulG, GR.mulI]) hW hctrs zs v S hctr htmp hin

/-- Negation of every coefficient. -/
theorem neg_exec {ins outs : Fin 1 → Fin T} {st ctr tmp : Fin T}
    (h : AutoLayout ins outs st ctr tmp) {W : ℕ} (hR : 3 ^ 2 ≤ A + 4) (hW : 1 ≤ W)
    {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W) (zs : List (GR W)) (v : HS T Q A U)
    (S : Stacks T A) (hctr : S.R ctr = ctrs) (htmp : S.R tmp = [])
    (hin : S.R (ins 0) = zs.flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ zs.length * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp (gaussAuto A ![![(-1, 0)]] 1 false)) (mk v S) m
        (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R (ins 0) = [] ∧
      S'.R (outs 0) = ((zs.map fun z => -z).flatMap (coeffSyms A W)).reverse ++ S.R (outs 0) ∧
      ∀ r, r ≠ ins 0 → r ≠ outs 0 → S'.R r = S.R r :=
  gaussAuto_exec_one body h (by norm_num at hR; omega) (gaussBound_one (-1) 0)
    (by norm_num at hR ⊢; omega) false
    (fun z => -z) (fun z => by rw [glin_mulG]; simp [GR.mulG, Prod.ext_iff]) hW hctrs zs v S
    hctr htmp hin

/-- Conjugation of every coefficient: the coefficient `-i` on the swapped parts. -/
theorem conj_exec {ins outs : Fin 1 → Fin T} {st ctr tmp : Fin T}
    (h : AutoLayout ins outs st ctr tmp) {W : ℕ} (hR : 3 ^ 2 ≤ A + 4) (hW : 1 ≤ W)
    {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W) (zs : List (GR W)) (v : HS T Q A U)
    (S : Stacks T A) (hctr : S.R ctr = ctrs) (htmp : S.R tmp = [])
    (hin : S.R (ins 0) = zs.flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ zs.length * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp (gaussAuto A ![![(0, -1)]] 1 true)) (mk v S) m
        (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R (ins 0) = [] ∧
      S'.R (outs 0) = ((zs.map GR.conj).flatMap (coeffSyms A W)).reverse ++ S.R (outs 0) ∧
      ∀ r, r ≠ ins 0 → r ≠ outs 0 → S'.R r = S.R r :=
  gaussAuto_exec_one body h (by norm_num at hR; omega) (gaussBound_one 0 (-1))
    (by norm_num at hR ⊢; omega) true GR.conj
    (fun z => by
      have := glin_mulG_conj 1 0 z
      rw [swapGR_true, this]
      simp [GR.mulG, GR.conj])
    hW hctrs zs v S hctr htmp hin

/-- Multiplication of every conjugated coefficient by `a + b i`: the coefficient `b - a i` on the
swapped parts. -/
theorem mulG_conj_exec {ins outs : Fin 1 → Fin T} {st ctr tmp : Fin T}
    (h : AutoLayout ins outs st ctr tmp) {W : ℕ} (a b : ℤ) (hA : 4 ≤ A)
    (hR : (2 * (b.natAbs + (-a).natAbs) + 1) ^ 2 ≤ A + 4) (hW : 1 ≤ W)
    {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W) (zs : List (GR W)) (v : HS T Q A U)
    (S : Stacks T A) (hctr : S.R ctr = ctrs) (htmp : S.R tmp = [])
    (hin : S.R (ins 0) = zs.flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ zs.length * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp
        (gaussAuto A ![![(b, -a)]] (b.natAbs + (-a).natAbs) true)) (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R (ins 0) = [] ∧
      S'.R (outs 0) = ((zs.map fun z => GR.mulG a b (GR.conj z)).flatMap (coeffSyms A W)).reverse ++
        S.R (outs 0) ∧
      ∀ r, r ≠ ins 0 → r ≠ outs 0 → S'.R r = S.R r :=
  gaussAuto_exec_one body h hA (gaussBound_one b (-a)) hR true _
    (fun z => glin_mulG_conj a b z) hW hctrs zs v S hctr htmp hin

/-- **The kernel butterfly on two coefficient streams.** Registers `ins 0`, `ins 1` hold the
coefficients `us`, `vs` of equal length; `outs 0`, `outs 1` gain the two outputs of
`GR.kernel2` on corresponding coefficients, reversed on top. -/
theorem kernel2_exec {ins outs : Fin 2 → Fin T} {st ctr tmp : Fin T}
    (h : AutoLayout ins outs st ctr tmp) {W : ℕ} (hR : 9 ^ 4 ≤ A + 4) (hW : 1 ≤ W)
    {ctrs : List (Fin (A + 4))} (hctrs : ctrs.length = W) (us vs : List (GR W))
    (hlen : vs.length = us.length) (v : HS T Q A U) (S : Stacks T A) (hctr : S.R ctr = ctrs)
    (htmp : S.R tmp = []) (hin₀ : S.R (ins 0) = us.flatMap (coeffSyms A W))
    (hin₁ : S.R (ins 1) = vs.flatMap (coeffSyms A W)) :
    ∃ v' m S', v'.user = v.user ∧ m ≤ us.length * (5 * W + 6) + 2 ∧
      Exec body (autoWords ins outs st ctr tmp (gaussAuto A gKernel2 4 false)) (mk v S) m
        (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R (ins 0) = [] ∧ S'.R (ins 1) = [] ∧
      S'.R (outs 0) = ((List.zipWith (fun u v => (GR.kernel2 u v).1) us vs).flatMap
        (coeffSyms A W)).reverse ++ S.R (outs 0) ∧
      S'.R (outs 1) = ((List.zipWith (fun u v => (GR.kernel2 u v).2) us vs).flatMap
        (coeffSyms A W)).reverse ++ S.R (outs 1) ∧
      ∀ r, r ∉ Set.range ins → r ∉ Set.range outs → S'.R r = S.R r := by
  have hB : ∀ j, ∑ i, (|(gKernel2 j i).1| + |(gKernel2 j i).2|) ≤ ((4 : ℕ) : ℤ) := by
    intro j
    fin_cases j <;> simp [gKernel2, Fin.sum_univ_two]
  have hcs : ∀ i, (![us, vs] i).length = us.length := by
    intro i; fin_cases i
    · rfl
    · exact hlen
  obtain ⟨v', m, S', hu, hm, he, hi, ho, hl, hins, houts, hoth⟩ :=
    gaussAuto_exec_list body h (by omega) hB (by simpa using hR) false hW hctrs ![us, vs] hcs
      v S hctr htmp (fun i => by fin_cases i <;> simp [hin₀, hin₁])
  have hz : ∀ (j : Fin 2) (c : Fin us.length),
      glin gKernel2
          (fun i => swapGR false ((![us, vs] i)[(c : ℕ)]'(by rw [hcs i]; exact c.isLt))) j =
        glin gKernel2 ![us[(c : ℕ)], vs[(c : ℕ)]'(by rw [hlen]; exact c.isLt)] j := by
    intro j c
    congr 1
    funext i
    fin_cases i <;> rfl
  refine ⟨v', m, S', hu, hm, he, hi, ho, hl, hins 0, hins 1, ?_, ?_, hoth⟩
  · rw [houts 0]
    congr 3
    apply List.ext_getElem (by simp [hlen])
    intro t _ _
    simp only [List.getElem_ofFn, List.getElem_zipWith, hz, glin_kernel2]
    rfl
  · rw [houts 1]
    congr 3
    apply List.ext_getElem (by simp [hlen])
    intro t _ _
    simp only [List.getElem_ofFn, List.getElem_zipWith, hz, glin_kernel2]
    rfl

end ExecInstances

end IntegerMultBounds.MathlibTM2.Layer
